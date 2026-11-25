import java.io.*;
import java.util.*;

public class HEG {
    // ---------- data (also used by NaiveMH) ----------
    static int m;                 // number of items
    static int[] itemId;          // item index -> original item id (indices follow increasing ids)
    static double[] invest;       // item index -> investment
    static int[][] tids;          // item index -> increasing ids of the transactions that contain it
    static double[][] utils;      // item index -> its utility in each of those transactions
    static int[][] trans;         // transaction -> item indices

    // ---------- efficiency cache: open addressing, 128-bit key (8 slots of 16 bits) -> efficiency ----------
    static long[] cHi, cLo; static boolean[] cUsed; static double[] cVals; static int cSize = 0;
    static long evaluations = 0, lookups = 0;

    // ---------- context: the transactions that contain the current pattern S, with S's utility in each ----------
    static int[] ctxT; static double[] ctxU; static int ctxLen = 0; static boolean ctxValid = false;
    static boolean sparse; static int[] mark; static int stamp = 0;

    static final String USAGE =
        "Usage: java HEG <db> <investments> <beta> <M> <samples> <burnIn> <seed> <outPrefix> [lambda]";

    public static void main(String[] a) throws Exception {
        if (a.length < 8 || a.length > 9) { System.err.println(USAGE); System.exit(2); }
        String dbF = a[0], invF = a[1], out = a[7];
        double beta = Double.parseDouble(a[2]);
        int M = Integer.parseInt(a[3]), keep = Integer.parseInt(a[4]), burn = Integer.parseInt(a[5]);
        long seed = Long.parseLong(a[6]);
        double lambda = a.length > 8 ? Double.parseDouble(a[8]) : 0.0;
        if (!(beta > 0) || Double.isInfinite(beta)) fail("beta must be a positive number");
        if (M < 2 || M > 8) fail("M must be between 2 and 8");
        if (M == 2 && lambda == 0) fail("M = 2 needs lambda > 0 (without bridge states a pair can never change)");
        if (keep < 1 || burn < 0) fail("samples must be >= 1 and burnIn >= 0");
        if (!(lambda >= 0) || Double.isInfinite(lambda)) fail("lambda must be >= 0");

        HeapSampler.start();
        long t0 = System.nanoTime();
        load(dbF, invF);
        double loadS = (System.nanoTime() - t0) / 1e9;
        checkLimits();
        initCache();

        // singleton efficiencies (used only by the bridge states)
        double[] effSingle = new double[m]; double ebar = 0;
        for (int i = 0; i < m; i++) {
            double u = 0; for (double v : utils[i]) u += v;
            effSingle[i] = u > 0 ? u / invest[i] : 0;
            ebar += pow(effSingle[i], beta);
        }
        ebar /= m;

        SplittableRandom rng = new SplittableRandom(seed);
        ctxT = new int[trans.length]; ctxU = new double[trans.length];
        sparse = m > 1000; mark = new int[m];

        // start: two distinct items of a random transaction, with positive efficiency
        int[] S = new int[M]; int s = 2; double effCur = 0;
        int[] multi = transactionsWithAtLeast(2);
        if (multi.length == 0) fail("no transaction has two or more items");
        for (int attempt = 0; attempt < 100000 && effCur <= 0; attempt++) {
            int[] T = trans[multi[rng.nextInt(multi.length)]];
            int x = rng.nextInt(T.length), y; do { y = rng.nextInt(T.length); } while (y == x);
            S[0] = Math.min(T[x], T[y]); S[1] = Math.max(T[x], T[y]);
            effCur = eff(S, 2);
        }
        if (effCur <= 0) fail("could not find a starting pair with positive utility");
        boolean[] inS = new boolean[m]; inS[S[0]] = true; inS[S[1]] = true;
        double wCur = pow(effCur, beta);   // target weight of the current state

        int[] order = new int[m]; for (int i = 0; i < m; i++) order[i] = i;
        int[] tmp = new int[M];
        double[] trace = new double[keep];
        HashMap<String, Rec> counts = new HashMap<>();
        long flips = 0, steps = 0;

        long t1 = System.nanoTime();
        int recorded = 0; long bridgeSweeps = 0, postBurnSweeps = 0, sweep;
        long maxSweeps = burn + 50L * keep;   // guard: stop if the chain sits in the bridge states too often
        for (sweep = 0; recorded < keep && sweep < maxSweeps; sweep++) {
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
                    if (s == M) continue;                       // S plus i is outside the window: weight 0
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
                steps++;
                boolean nowIn = rng.nextDouble() < wIn / (wIn + wOut);
                if (nowIn != inS[i]) {                          // the pattern changes: adopt tmp
                    flips++;
                    System.arraycopy(tmp, 0, S, 0, k); s = k; inS[i] = nowIn;
                    if (nowIn) { effCur = effIn; wCur = wIn; } else { effCur = effOut; wCur = wOut; }
                    if (nowIn && ctxValid && s >= 2) extendContext(i); else ctxValid = false;
                }
            }
            if (sweep >= burn) {
                postBurnSweeps++;
                if (s < 2) { bridgeSweeps++; continue; }       // bridge state: not recorded
                trace[recorded++] = effCur;
                StringBuilder kb = new StringBuilder();
                for (int j = 0; j < s; j++) { if (j > 0) kb.append(' '); kb.append(itemId[S[j]]); }
                String key = kb.toString();
                Rec r = counts.get(key); if (r == null) counts.put(key, new Rec(effCur)); else r.c++;
            }
        }
        double sampleS = (System.nanoTime() - t1) / 1e9;
        if (recorded == 0) fail("no pattern was recorded in " + sweep + " sweeps: the chain stayed in the bridge states (lower lambda)");
        if (recorded < keep) {
            System.err.println("WARNING: only " + recorded + " of " + keep + " samples were recorded (bridge share too high; lower lambda)");
            trace = Arrays.copyOf(trace, recorded);
        }

        long t2 = System.nanoTime();
        try (PrintWriter w = new PrintWriter(new BufferedWriter(new FileWriter(out + "_trace.txt")))) {
            for (double v : trace) w.println(v);
        }
        try (PrintWriter w = new PrintWriter(new BufferedWriter(new FileWriter(out + "_counts.txt")))) {
            for (Map.Entry<String, Rec> e : counts.entrySet()) w.println(e.getValue().c + "\t" + e.getValue().e + "\t" + e.getKey());
        }
        double writeS = (System.nanoTime() - t2) / 1e9;
        double peakMB = HeapSampler.stop();
        System.out.printf(Locale.ROOT,
            "{\"program\":\"HEG\",\"items\":%d,\"transactions\":%d,\"beta\":%s,\"M\":%d,\"lambda\":%s,\"seed\":%d," +
            "\"load_s\":%.3f,\"sample_s\":%.3f,\"write_s\":%.3f,\"time_s\":%.3f,\"sweeps\":%d,\"recorded\":%d,\"requested\":%d," +
            "\"bridge_share\":%.4f,\"flip_rate\":%.4f,\"evaluations\":%d,\"lookups\":%d," +
            "\"distinct_patterns\":%d,\"median_eff\":%.10g,\"peak_heap_MB\":%.1f,\"peak_after_gc_MB\":%.1f,\"gc_count\":%d}%n",
            m, trans.length, fmt(beta), M, fmt(lambda), seed,
            loadS, sampleS, writeS, loadS + sampleS, sweep, recorded, keep,
            postBurnSweeps > 0 ? (double) bridgeSweeps / postBurnSweeps : 0.0, steps > 0 ? (double) flips / steps : 0.0,
            evaluations, lookups, counts.size(), median(trace), peakMB, HeapSampler.peakAfterGcMB(), HeapSampler.collections());
    }

    static final class Rec { int c = 1; final double e; Rec(double e) { this.e = e; } }  // count and efficiency of a recorded pattern

    // ---------- helpers shared with NaiveMH ----------
    static void fail(String msg) { System.err.println("ERROR: " + msg); System.exit(1); }
    static String fmt(double v) { return String.format(Locale.ROOT, "%.10g", v); }
    static double pow(double v, double beta) { return beta == 1.0 ? v : (beta == 2.0 ? v * v : Math.pow(v, beta)); }

    static double median(double[] x) {
        if (x.length == 0) return 0.0;
        double[] s = x.clone(); Arrays.sort(s); int n = s.length;
        return n % 2 == 1 ? s[n / 2] : 0.5 * (s[n / 2 - 1] + s[n / 2]);
    }

    static void checkLimits() {
        if (m >= 65535) fail("this implementation supports fewer than 65,535 distinct items (found " + m + ")");
    }

    static void initCache() {
        cHi = new long[1 << 16]; cLo = new long[1 << 16]; cUsed = new boolean[1 << 16]; cVals = new double[1 << 16];
        cSize = 0; evaluations = 0; lookups = 0;
    }

    static int[] transactionsWithAtLeast(int len) {
        int c = 0; for (int[] t : trans) if (t.length >= len) c++;
        int[] r = new int[c]; c = 0;
        for (int t = 0; t < trans.length; t++) if (trans[t].length >= len) r[c++] = t;
        return r;
    }

    // pattern key: item index + 1 in 16-bit slots (slots 0-3 in lo, 4-7 in hi); unique for M <= 8 and m < 65,535
    static long keyHi(int[] p, int k) { long h = 0; for (int j = 4; j < k; j++) h |= ((long) (p[j] + 1)) << (16 * (j - 4)); return h; }
    static long keyLo(int[] p, int k) { long l = 0; for (int j = 0; j < k && j < 4; j++) l |= ((long) (p[j] + 1)) << (16 * j); return l; }
    static int slot(long hi, long lo) { return (int) (mix(hi * 0x9E3779B97F4A7C15L ^ lo) & (cHi.length - 1)); }

    /** Efficiency of the sorted pattern p[0..k-1] (k >= 2), memoised. */
    static double eff(int[] p, int k) {
        long hi = keyHi(p, k), lo = keyLo(p, k);
        lookups++;
        int mask = cHi.length - 1, h = slot(hi, lo);
        while (cUsed[h]) { if (cHi[h] == hi && cLo[h] == lo) return cVals[h]; h = (h + 1) & mask; }
        evaluations++;
        double u = utility(p, k), inv = 0;
        for (int j = 0; j < k; j++) inv += invest[p[j]];
        double e = u > 0 ? u / inv : 0.0;
        cUsed[h] = true; cHi[h] = hi; cLo[h] = lo; cVals[h] = e;
        if (++cSize * 2 > cHi.length) grow();
        return e;
    }

    /** Efficiency of S plus item (sorted p[0..k-1]) from the context of S: only transactions containing S are scanned. */
    static double effAdd(int[] p, int k, int item, int[] S, int s) {
        long hi = keyHi(p, k), lo = keyLo(p, k);
        lookups++;
        int mask = cHi.length - 1, h = slot(hi, lo);
        while (cUsed[h]) { if (cHi[h] == hi && cLo[h] == lo) return cVals[h]; h = (h + 1) & mask; }
        evaluations++;
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
        cUsed[h] = true; cHi[h] = hi; cLo[h] = lo; cVals[h] = e;
        if (++cSize * 2 > cHi.length) grow();
        return e;
    }

    /** Rebuild the context for pattern p[0..k-1] (k-way intersection of the items' transaction lists). */
    static void buildContext(int[] p, int k) {
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

    /** Mark every item that occurs in a transaction of the context. */
    static void remark() {
        stamp++;
        for (int x = 0; x < ctxLen; x++) for (int it : trans[ctxT[x]]) mark[it] = stamp;
    }

    /** After adding item: keep only the transactions that also contain it, and add its utility. */
    static void extendContext(int item) {
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

    static long mix(long z) { z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL; z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L; return z ^ (z >>> 33); }

    static void grow() {
        long[] oh = cHi, ol = cLo; boolean[] ou = cUsed; double[] ov = cVals; int n = oh.length * 2;
        cHi = new long[n]; cLo = new long[n]; cUsed = new boolean[n]; cVals = new double[n];
        int mask = n - 1;
        for (int i = 0; i < oh.length; i++) if (ou[i]) {
            int h = slot(oh[i], ol[i]);
            while (cUsed[h]) h = (h + 1) & mask;
            cUsed[h] = true; cHi[h] = oh[i]; cLo[h] = ol[i]; cVals[h] = ov[i];
        }
    }

    /** U(p): sum of the pattern's utilities over the transactions that contain all its items. */
    static double utility(int[] p, int k) {
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

    /** Smallest index >= from with a[index] >= target (exponential then binary search). */
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

    /** Read the investments and the database; items are indexed in increasing order of their ids. */
    static void load(String dbF, String invF) throws IOException {
        TreeMap<Integer, Double> inv = new TreeMap<>();
        try (BufferedReader r = new BufferedReader(new FileReader(invF))) {
            String line; int ln = 0;
            while ((line = r.readLine()) != null) {
                ln++; line = line.trim();
                if (line.isEmpty() || line.charAt(0) == '#' || line.charAt(0) == '%' || line.charAt(0) == '@') continue;
                String[] f = line.split("\\s+");
                if (f.length < 2) fail("investment file line " + ln + ": expected \"item value\"");
                double v = Double.parseDouble(f[1]);
                if (!(v > 0) || Double.isInfinite(v)) fail("investment of item " + f[0] + " must be positive (line " + ln + ")");
                if (inv.put(Integer.parseInt(f[0]), v) != null) fail("item " + f[0] + " appears twice in the investment file");
            }
        }
        m = inv.size(); itemId = new int[m]; invest = new double[m];
        HashMap<Integer, Integer> idx = new HashMap<>();
        int c = 0; for (Map.Entry<Integer, Double> e : inv.entrySet()) { itemId[c] = e.getKey(); invest[c] = e.getValue(); idx.put(e.getKey(), c++); }
        int[] cap = new int[m]; int[][] tt = new int[m][]; double[][] uu = new double[m][]; int[] len = new int[m];
        for (int i = 0; i < m; i++) { cap[i] = 16; tt[i] = new int[16]; uu[i] = new double[16]; }
        int[] seen = new int[m]; Arrays.fill(seen, -1);
        ArrayList<int[]> tr = new ArrayList<>();
        try (BufferedReader r = new BufferedReader(new FileReader(dbF), 1 << 20)) {
            String line; int t = 0;
            while ((line = r.readLine()) != null) {
                if (line.isEmpty() || line.charAt(0) == '#' || line.charAt(0) == '%' || line.charAt(0) == '@') continue;
                String[] f = line.split(":");
                if (f.length != 3) fail("database line " + (t + 1) + ": expected \"items:TU:utilities\"");
                String[] it = f[0].trim().split(" "), ut = f[2].trim().split(" ");
                if (it.length != ut.length) fail("database line " + (t + 1) + ": numbers of items and utilities differ");
                int[] row = new int[it.length];
                for (int q = 0; q < it.length; q++) {
                    Integer ix = idx.get(Integer.parseInt(it[q]));
                    if (ix == null) fail("item " + it[q] + " (database line " + (t + 1) + ") has no investment");
                    int i = ix;
                    if (seen[i] == t) fail("item " + it[q] + " appears twice in database line " + (t + 1));
                    seen[i] = t;
                    double u = Double.parseDouble(ut[q]);
                    if (!(u >= 0) || Double.isInfinite(u)) fail("negative or invalid utility in database line " + (t + 1));
                    if (len[i] == cap[i]) { cap[i] *= 2; tt[i] = Arrays.copyOf(tt[i], cap[i]); uu[i] = Arrays.copyOf(uu[i], cap[i]); }
                    tt[i][len[i]] = t; uu[i][len[i]] = u; len[i]++;
                    row[q] = i;
                }
                tr.add(row); t++;
            }
        }
        tids = new int[m][]; utils = new double[m][];
        for (int i = 0; i < m; i++) { tids[i] = Arrays.copyOf(tt[i], len[i]); utils[i] = Arrays.copyOf(uu[i], len[i]); }
        trans = tr.toArray(new int[0][]);
    }
}
