import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.SplittableRandom;
import java.util.TreeMap;
import java.util.concurrent.ThreadLocalRandom;


public final class HEG {

    public static final double DEFAULT_BETA = 2.0;
    public static final int DEFAULT_MAX_LENGTH = 5;
    public static final int DEFAULT_SAMPLES = 6000;
    public static final int DEFAULT_BURN_IN = 600;
    public static final double DEFAULT_BRIDGE = 0.1;

    static final String USAGE = String.join(System.lineSeparator(),
        "Usage: java HEG <database> <investments> <output> [options]",
        "",
        "  <database>     transactions in SPMF utility format, one per line: items:transaction utility:utilities",
        "  <investments>  the investment of every item, one \"item investment\" pair per line",
        "  <output>       file for the sampled patterns, one per line: items #EFFICIENCY: efficiency",
        "",
        "Options (the defaults are the settings of the paper):",
        "  --beta <beta>      focus exponent: patterns are drawn in proportion to Eff^beta (default 2)",
        "  --max-length <M>   maximum pattern length, from 2 to 8 (default 5)",
        "  --samples <N>      number of sampled patterns (default 6000)",
        "  --burn-in <B>      number of first sweeps that are discarded (default 600)",
        "  --bridge <c>       bridge factor: the bridge states weigh c^beta; 0 removes them (default 0.1)",
        "  --seed <seed>      random seed; the same seed gives the same sample (default: a random seed)");

    // ---------- the database ----------
    private final int m;                 // number of items
    private final int[] itemId;          // item index -> item id (the indices follow increasing ids)
    private final double[] invest;       // item index -> investment
    private final int[][] tids;          // item index -> increasing indices of the transactions that contain the item
    private final double[][] utils;      // item index -> the item's utility in each of these transactions
    private final int[][] trans;         // transaction -> its item indices
    private final int[] multi;           // the transactions with at least two items (a chain starts in one of them)
    private final double[] effSingle;    // item index -> Eff({i}), used by the bridge states

    /** Receives the sampled patterns, in the order in which they are drawn. */
    public interface Sink {
        /**
         * @param items      the ids of the pattern's items, in increasing order
         * @param efficiency the efficiency of the pattern
         */
        void accept(int[] items, double efficiency) throws IOException;
    }

    /** Summary of a run. */
    public static final class Result {
        /** Number of sampled patterns (fewer than requested only if the chain stayed too long in the bridge states). */
        public final int samples;
        /** Number of sweeps, burn-in included. */
        public final long sweeps;
        /** Share of the sweeps after the burn-in that ended in a bridge state; such a sweep records nothing. */
        public final double bridgeShare;

        Result(int samples, long sweeps, double bridgeShare) {
            this.samples = samples; this.sweeps = sweeps; this.bridgeShare = bridgeShare;
        }
    }

    /**
     * Reads a database in SPMF utility format ({@code items:transaction utility:utilities}, one transaction per
     * line; decimal utilities are accepted) and its investment file (one {@code item investment} pair per line).
     * Every item of the database needs a positive investment. Lines that start with #, % or @ are ignored.
     */
    public HEG(String databaseFile, String investmentFile) throws IOException {
        TreeMap<Integer, Double> inv = new TreeMap<>();
        try (BufferedReader r = new BufferedReader(new FileReader(investmentFile))) {
            String line; int ln = 0;
            while ((line = r.readLine()) != null) {
                ln++; line = line.trim();
                if (ignored(line)) continue;
                String[] f = line.split("\\s+");
                if (f.length < 2) throw error(investmentFile, ln, "expected \"item investment\"");
                int id = toInt(f[0], investmentFile, ln);
                double v = toDouble(f[1], investmentFile, ln);
                if (!(v > 0) || Double.isInfinite(v)) throw error(investmentFile, ln, "the investment of item " + id + " must be positive");
                if (inv.put(id, v) != null) throw error(investmentFile, ln, "item " + id + " is listed twice");
            }
        }
        m = inv.size();
        if (m == 0) throw new IllegalArgumentException(investmentFile + ": no investment found");
        if (m >= 65535) throw new IllegalArgumentException("at most 65,534 distinct items are supported (found " + m + ")");
        itemId = new int[m]; invest = new double[m];
        HashMap<Integer, Integer> idx = new HashMap<>();
        int c = 0;
        for (Map.Entry<Integer, Double> e : inv.entrySet()) { itemId[c] = e.getKey(); invest[c] = e.getValue(); idx.put(e.getKey(), c++); }

        int[] cap = new int[m], len = new int[m], seen = new int[m];
        int[][] tt = new int[m][]; double[][] uu = new double[m][];
        for (int i = 0; i < m; i++) { cap[i] = 16; tt[i] = new int[16]; uu[i] = new double[16]; }
        Arrays.fill(seen, -1);
        ArrayList<int[]> rows = new ArrayList<>();
        try (BufferedReader r = new BufferedReader(new FileReader(databaseFile), 1 << 20)) {
            String line; int ln = 0, t = 0;
            while ((line = r.readLine()) != null) {
                ln++; line = line.trim();
                if (ignored(line)) continue;
                String[] f = line.split(":");
                if (f.length != 3) throw error(databaseFile, ln, "expected \"items:transaction utility:utilities\"");
                String[] it = f[0].trim().split("\\s+"), ut = f[2].trim().split("\\s+");
                if (it.length != ut.length) throw error(databaseFile, ln, "the numbers of items and utilities differ");
                int[] row = new int[it.length];
                for (int q = 0; q < it.length; q++) {
                    int id = toInt(it[q], databaseFile, ln);
                    Integer ix = idx.get(id);
                    if (ix == null) throw error(databaseFile, ln, "item " + id + " has no investment");
                    int i = ix;
                    if (seen[i] == t) throw error(databaseFile, ln, "item " + id + " appears twice");
                    seen[i] = t;
                    double u = toDouble(ut[q], databaseFile, ln);
                    if (!(u >= 0) || Double.isInfinite(u)) throw error(databaseFile, ln, "utilities must be non-negative numbers");
                    if (len[i] == cap[i]) { cap[i] *= 2; tt[i] = Arrays.copyOf(tt[i], cap[i]); uu[i] = Arrays.copyOf(uu[i], cap[i]); }
                    tt[i][len[i]] = t; uu[i][len[i]] = u; len[i]++;
                    row[q] = i;
                }
                rows.add(row); t++;
            }
        }
        tids = new int[m][]; utils = new double[m][];
        for (int i = 0; i < m; i++) { tids[i] = Arrays.copyOf(tt[i], len[i]); utils[i] = Arrays.copyOf(uu[i], len[i]); }
        trans = rows.toArray(new int[0][]);

        int n2 = 0; for (int[] row : trans) if (row.length >= 2) n2++;
        multi = new int[n2]; n2 = 0;
        for (int t = 0; t < trans.length; t++) if (trans[t].length >= 2) multi[n2++] = t;

        effSingle = new double[m];
        for (int i = 0; i < m; i++) {
            double u = 0; for (double v : utils[i]) u += v;
            effSingle[i] = u > 0 ? u / invest[i] : 0;
        }
    }

    /**
     * Draws {@code samples} patterns from the distribution proportional to Eff(P)^beta on 2 &lt;= |P| &lt;= maxLength
     * and passes each one to {@code sink}, in the order drawn.
     *
     * @param beta      focus exponent (beta &gt; 0)
     * @param maxLength maximum pattern length M, from 2 to 8
     * @param samples   number of patterns to draw, N
     * @param burnIn    number of first sweeps that are discarded, B
     * @param bridge    bridge factor c &gt;= 0: the single items and the empty pattern are bridge states with weight
     *                  c^beta * Eff({i})^beta and c^beta * mean(Eff({i})^beta); they are never recorded. 0 removes them
     * @param seed      random seed; the same seed and parameters give the same sample
     */
    public Result sample(double beta, int maxLength, int samples, int burnIn, double bridge, long seed, Sink sink) throws IOException {
        if (!(beta > 0) || Double.isInfinite(beta)) throw new IllegalArgumentException("beta must be a positive number");
        if (maxLength < 2 || maxLength > 8) throw new IllegalArgumentException("the maximum length must be between 2 and 8");
        if (samples < 1) throw new IllegalArgumentException("the number of samples must be at least 1");
        if (burnIn < 0) throw new IllegalArgumentException("the burn-in must be at least 0");
        if (!(bridge >= 0) || Double.isInfinite(bridge)) throw new IllegalArgumentException("the bridge factor must be a number >= 0");
        double lambda = bridgeWeight(bridge, beta);
        if (bridge > 0 && !(lambda > 0 && lambda < Double.POSITIVE_INFINITY))
            throw new IllegalArgumentException("the bridge weight c^beta is out of range");
        if (maxLength == 2 && lambda == 0)
            throw new IllegalArgumentException("a maximum length of 2 needs bridge states (a bridge factor > 0): without them a pair can never change");
        if (multi.length == 0) throw new IllegalArgumentException("no transaction has two or more items");
        return new Chain(beta, maxLength, lambda, seed).run(samples, burnIn, sink);
    }

    /**
     * Weight of the bridge states, lambda = c^beta, rounded to 6 significant digits, so that c = 0.1 and beta = 2 give
     * exactly 0.01, the value used in the paper (a given seed then reproduces the paper's chains).
     */
    static double bridgeWeight(double c, double beta) {
        if (c == 0) return 0;
        return Double.parseDouble(String.format(Locale.ROOT, "%.6g", Math.pow(c, beta)));
    }

    /** One Markov chain, with its random generator, its cache of efficiencies and the context of its current pattern. */
    private final class Chain {
        private final double beta, lambda;
        private final int M;
        private final SplittableRandom rng;

        // efficiency cache: open addressing; a pattern's key holds item index + 1 in 8 slots of 16 bits (0-3 in lo, 4-7 in hi)
        private long[] cHi = new long[1 << 16], cLo = new long[1 << 16];
        private boolean[] cUsed = new boolean[1 << 16];
        private double[] cVals = new double[1 << 16];
        private int cSize = 0;

        // context: the transactions that contain the current pattern S, with S's utility in each
        private final int[] ctxT = new int[trans.length];
        private final double[] ctxU = new double[trans.length];
        private int ctxLen = 0;
        private boolean ctxValid = false;

        // on sparse data, the items that occur in a transaction of the context carry the current stamp
        private final boolean sparse = m > 1000;
        private final int[] mark = new int[m];
        private int stamp = 0;

        Chain(double beta, int M, double lambda, long seed) {
            this.beta = beta; this.M = M; this.lambda = lambda; this.rng = new SplittableRandom(seed);
        }

        Result run(int samples, int burnIn, Sink sink) throws IOException {
            double ebar = 0;
            for (int i = 0; i < m; i++) ebar += pow(effSingle[i], beta);
            ebar /= m;

            // start: two distinct items of a random transaction, with positive efficiency
            int[] S = new int[M]; int s = 2; double effCur = 0;
            for (int attempt = 0; attempt < 100000 && effCur <= 0; attempt++) {
                int[] T = trans[multi[rng.nextInt(multi.length)]];
                int x = rng.nextInt(T.length), y;
                do { y = rng.nextInt(T.length); } while (y == x);
                S[0] = Math.min(T[x], T[y]); S[1] = Math.max(T[x], T[y]);
                effCur = eff(S, 2);
            }
            if (effCur <= 0) throw new IllegalStateException("no starting pair with positive utility was found");
            boolean[] inS = new boolean[m]; inS[S[0]] = true; inS[S[1]] = true;
            double wCur = pow(effCur, beta);   // target weight of the current state

            int[] order = new int[m]; for (int i = 0; i < m; i++) order[i] = i;
            int[] tmp = new int[M];
            int recorded = 0; long sweep, bridgeSweeps = 0, postBurnSweeps = 0;
            long maxSweeps = burnIn + 50L * samples;   // stops a chain that stays in the bridge states too often
            for (sweep = 0; recorded < samples && sweep < maxSweeps; sweep++) {
                for (int i = m - 1; i > 0; i--) { int j = rng.nextInt(i + 1); int w = order[i]; order[i] = order[j]; order[j] = w; }
                for (int oi = 0; oi < m; oi++) {
                    int i = order[oi];
                    double wIn, wOut, effIn = 0, effOut = 0; int k;
                    if (inS[i]) {                                   // compare S with S minus i
                        if (s == 2 && lambda == 0) continue;        // S minus i has weight 0: i stays in
                        k = 0; for (int j = 0; j < s; j++) if (S[j] != i) tmp[k++] = S[j];
                        wIn = wCur;
                        if (k >= 2) { effOut = eff(tmp, k); wOut = pow(effOut, beta); }
                        else if (k == 1) { effOut = effSingle[tmp[0]]; wOut = lambda * pow(effOut, beta); }
                        else { wOut = lambda * ebar; }
                    } else {                                        // compare S plus i with S
                        if (s == M) continue;                       // S plus i is longer than M: weight 0
                        if (sparse && s >= 1) {                     // S plus i never occurs: weight 0
                            if (!ctxValid) { buildContext(S, s); ctxValid = true; }
                            if (mark[i] != stamp) continue;
                        }
                        k = 0; boolean put = false;
                        for (int j = 0; j < s; j++) { if (!put && i < S[j]) { tmp[k++] = i; put = true; } tmp[k++] = S[j]; }
                        if (!put) tmp[k++] = i;
                        if (k >= 2) { effIn = effAdd(tmp, k, i, S, s); wIn = pow(effIn, beta); }
                        else { effIn = effSingle[i]; wIn = lambda * pow(effIn, beta); }
                        wOut = wCur;
                    }
                    if (wIn + wOut <= 0) continue;
                    boolean nowIn = rng.nextDouble() < wIn / (wIn + wOut);   // Gibbs update of item i
                    if (nowIn != inS[i]) {                                   // the pattern changes: adopt tmp
                        System.arraycopy(tmp, 0, S, 0, k); s = k; inS[i] = nowIn;
                        if (nowIn) { effCur = effIn; wCur = wIn; } else { effCur = effOut; wCur = wOut; }
                        if (nowIn && ctxValid && s >= 2) extendContext(i); else ctxValid = false;
                    }
                }
                if (sweep >= burnIn) {
                    postBurnSweeps++;
                    if (s < 2) { bridgeSweeps++; continue; }       // a bridge state is not recorded
                    int[] p = new int[s];
                    for (int j = 0; j < s; j++) p[j] = itemId[S[j]];
                    sink.accept(p, effCur);
                    recorded++;
                }
            }
            if (recorded == 0)
                throw new IllegalStateException("no pattern was recorded in " + sweep + " sweeps: the chain stayed in the bridge states (lower the bridge factor)");
            return new Result(recorded, sweep, postBurnSweeps > 0 ? (double) bridgeSweeps / postBurnSweeps : 0.0);
        }

        private int slot(long hi, long lo) { return (int) (mix(hi * 0x9E3779B97F4A7C15L ^ lo) & (cHi.length - 1)); }

        /** Efficiency of the sorted pattern p[0..k-1] (k &gt;= 2), computed once and then read from the cache. */
        private double eff(int[] p, int k) {
            long hi = keyHi(p, k), lo = keyLo(p, k);
            int mask = cHi.length - 1, h = slot(hi, lo);
            while (cUsed[h]) { if (cHi[h] == hi && cLo[h] == lo) return cVals[h]; h = (h + 1) & mask; }
            double u = utility(p, k), inv = 0;
            for (int j = 0; j < k; j++) inv += invest[p[j]];
            double e = u > 0 ? u / inv : 0.0;
            store(h, hi, lo, e);
            return e;
        }

        /** Efficiency of S plus item (the sorted pattern p[0..k-1]), from the context of S: only the transactions that contain S are scanned. */
        private double effAdd(int[] p, int k, int item, int[] S, int s) {
            long hi = keyHi(p, k), lo = keyLo(p, k);
            int mask = cHi.length - 1, h = slot(hi, lo);
            while (cUsed[h]) { if (cHi[h] == hi && cLo[h] == lo) return cVals[h]; h = (h + 1) & mask; }
            if (!ctxValid) { buildContext(S, s); ctxValid = true; }
            int[] lt = tids[item]; double[] lu = utils[item];
            double u = 0; int q = 0;
            for (int x = 0; x < ctxLen; x++) {
                q = gallop(lt, q, ctxT[x]);
                if (q >= lt.length) break;
                if (lt[q] == ctxT[x]) u += ctxU[x] + lu[q];
            }
            double inv = 0; for (int j = 0; j < k; j++) inv += invest[p[j]];
            double e = u > 0 ? u / inv : 0.0;
            store(h, hi, lo, e);
            return e;
        }

        private void store(int h, long hi, long lo, double e) {
            cUsed[h] = true; cHi[h] = hi; cLo[h] = lo; cVals[h] = e;
            if (++cSize * 2 > cHi.length) grow();
        }

        private void grow() {
            long[] oh = cHi, ol = cLo; boolean[] ou = cUsed; double[] ov = cVals; int n = oh.length * 2;
            cHi = new long[n]; cLo = new long[n]; cUsed = new boolean[n]; cVals = new double[n];
            int mask = n - 1;
            for (int i = 0; i < oh.length; i++) if (ou[i]) {
                int h = slot(oh[i], ol[i]);
                while (cUsed[h]) h = (h + 1) & mask;
                cUsed[h] = true; cHi[h] = oh[i]; cLo[h] = ol[i]; cVals[h] = ov[i];
            }
        }

        /** Rebuilds the context for the pattern p[0..k-1] (intersection of its items' transaction lists). */
        private void buildContext(int[] p, int k) {
            int d = 0;
            for (int j = 1; j < k; j++) if (tids[p[j]].length < tids[p[d]].length) d = j;
            int[] dt = tids[p[d]]; double[] du = utils[p[d]];
            int[] pos = new int[k]; ctxLen = 0;
            outer:
            for (int x = 0; x < dt.length; x++) {
                int t = dt[x]; double sum = du[x];
                for (int j = 0; j < k; j++) {
                    if (j == d) continue;
                    int[] lt = tids[p[j]];
                    int q = gallop(lt, pos[j], t); pos[j] = q;
                    if (q >= lt.length) break outer;
                    if (lt[q] != t) continue outer;
                    sum += utils[p[j]][q];
                }
                ctxT[ctxLen] = t; ctxU[ctxLen] = sum; ctxLen++;
            }
            if (sparse) remark();
        }

        /** After adding item: keeps only the transactions that also contain it, and adds its utility. */
        private void extendContext(int item) {
            int[] lt = tids[item]; double[] lu = utils[item];
            int w = 0, q = 0;
            for (int x = 0; x < ctxLen; x++) {
                q = gallop(lt, q, ctxT[x]);
                if (q >= lt.length) break;
                if (lt[q] == ctxT[x]) { ctxT[w] = ctxT[x]; ctxU[w] = ctxU[x] + lu[q]; w++; }
            }
            ctxLen = w;
            if (sparse) remark();
        }

        /** Marks every item that occurs in a transaction of the context. */
        private void remark() {
            stamp++;
            for (int x = 0; x < ctxLen; x++) for (int it : trans[ctxT[x]]) mark[it] = stamp;
        }
    }

    /** U(p): the sum of the pattern's utilities over the transactions that contain all its items. */
    private double utility(int[] p, int k) {
        int d = 0;
        for (int j = 1; j < k; j++) if (tids[p[j]].length < tids[p[d]].length) d = j;
        int[] dt = tids[p[d]]; double[] du = utils[p[d]];
        int[] pos = new int[k];
        double total = 0;
        outer:
        for (int x = 0; x < dt.length; x++) {
            int t = dt[x]; double sum = du[x];
            for (int j = 0; j < k; j++) {
                if (j == d) continue;
                int[] lt = tids[p[j]];
                int q = gallop(lt, pos[j], t); pos[j] = q;
                if (q >= lt.length) break outer;
                if (lt[q] != t) continue outer;
                sum += utils[p[j]][q];
            }
            total += sum;
        }
        return total;
    }

    static double pow(double v, double beta) { return beta == 1.0 ? v : (beta == 2.0 ? v * v : Math.pow(v, beta)); }

    static long keyHi(int[] p, int k) { long h = 0; for (int j = 4; j < k; j++) h |= ((long) (p[j] + 1)) << (16 * (j - 4)); return h; }

    static long keyLo(int[] p, int k) { long l = 0; for (int j = 0; j < k && j < 4; j++) l |= ((long) (p[j] + 1)) << (16 * j); return l; }

    static long mix(long z) { z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL; z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L; return z ^ (z >>> 33); }

    /** Smallest index &gt;= from with a[index] &gt;= target (exponential, then binary search). */
    static int gallop(int[] a, int from, int target) {
        int n = a.length;
        if (from >= n || a[from] >= target) return from;
        int lo = from, step = 1, hi = from + 1;
        while (hi < n && a[hi] < target) { lo = hi; step <<= 1; hi = lo + step; }
        if (hi > n) hi = n;
        int L = lo + 1, R = hi;
        while (L < R) { int mid = (L + R) >>> 1; if (a[mid] < target) L = mid + 1; else R = mid; }
        return L;
    }

    private static boolean ignored(String line) {
        return line.isEmpty() || line.charAt(0) == '#' || line.charAt(0) == '%' || line.charAt(0) == '@';
    }

    private static IllegalArgumentException error(String file, int line, String msg) {
        return new IllegalArgumentException(file + ", line " + line + ": " + msg);
    }

    private static int toInt(String s, String file, int line) {
        try { return Integer.parseInt(s); } catch (NumberFormatException e) { throw error(file, line, "\"" + s + "\" is not an item id"); }
    }

    private static double toDouble(String s, String file, int line) {
        try { return Double.parseDouble(s); } catch (NumberFormatException e) { throw error(file, line, "\"" + s + "\" is not a number"); }
    }

    // ---------- command line ----------
    public static void main(String[] args) {
        if (args.length == 0 || args[0].equals("-h") || args[0].equals("--help")) { System.out.println(USAGE); return; }
        if (args.length < 3) { System.err.println(USAGE); System.exit(2); }
        try {
            double beta = DEFAULT_BETA, bridge = DEFAULT_BRIDGE;
            int maxLength = DEFAULT_MAX_LENGTH, samples = DEFAULT_SAMPLES, burnIn = DEFAULT_BURN_IN;
            long seed = ThreadLocalRandom.current().nextInt(Integer.MAX_VALUE);   // printed at the end, to repeat the run
            for (int a = 3; a < args.length; a += 2) {
                String opt = args[a];
                if (a + 1 >= args.length) throw new IllegalArgumentException("option " + opt + " needs a value");
                String v = args[a + 1];
                switch (opt) {
                    case "--beta":       beta = number(opt, v); break;
                    case "--max-length": maxLength = (int) whole(opt, v, Integer.MIN_VALUE, Integer.MAX_VALUE); break;
                    case "--samples":    samples = (int) whole(opt, v, Integer.MIN_VALUE, Integer.MAX_VALUE); break;
                    case "--burn-in":    burnIn = (int) whole(opt, v, Integer.MIN_VALUE, Integer.MAX_VALUE); break;
                    case "--bridge":     bridge = number(opt, v); break;
                    case "--seed":       seed = whole(opt, v, Long.MIN_VALUE, Long.MAX_VALUE); break;
                    default: throw new IllegalArgumentException("unknown option " + opt + " (run java HEG without arguments to see the options)");
                }
            }
            HEG heg = new HEG(args[0], args[1]);
            File out = new File(args[2]);
            File dir = out.getAbsoluteFile().getParentFile();
            if (dir != null && !dir.isDirectory() && !dir.mkdirs()) throw new IOException("cannot create the folder " + dir);
            Result r;
            try (BufferedWriter w = new BufferedWriter(new FileWriter(out), 1 << 16)) {
                StringBuilder line = new StringBuilder();
                r = heg.sample(beta, maxLength, samples, burnIn, bridge, seed, (items, eff) -> {
                    line.setLength(0);
                    for (int j = 0; j < items.length; j++) { if (j > 0) line.append(' '); line.append(items[j]); }
                    line.append(" #EFFICIENCY: ").append(eff);
                    w.append(line); w.newLine();
                });
            }
            System.out.printf(Locale.ROOT, "%d patterns written to %s (seed %d; %d sweeps; %.1f%% of the sweeps after the burn-in ended in a bridge state)%n",
                r.samples, args[2], seed, r.sweeps, 100 * r.bridgeShare);
            if (r.samples < samples)
                System.err.println("WARNING: only " + r.samples + " of " + samples + " patterns were sampled: the chain stayed too long in the bridge states (lower --bridge)");
        } catch (IllegalArgumentException | IllegalStateException | IOException e) {
            System.err.println("ERROR: " + e.getMessage());
            System.exit(1);
        }
    }

    private static double number(String opt, String v) {
        try { return Double.parseDouble(v); } catch (NumberFormatException e) { throw new IllegalArgumentException(opt + ": \"" + v + "\" is not a number"); }
    }

    private static long whole(String opt, String v, long min, long max) {
        long x;
        try { x = Long.parseLong(v); } catch (NumberFormatException e) { throw new IllegalArgumentException(opt + ": \"" + v + "\" is not a whole number"); }
        if (x < min || x > max) throw new IllegalArgumentException(opt + ": " + v + " is out of range");
        return x;
    }
}
