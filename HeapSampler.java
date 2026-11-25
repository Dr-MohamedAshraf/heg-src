import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.lang.management.MemoryUsage;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class HeapSampler implements Runnable {
    static final int PERIOD_MS = 5;
    private static volatile boolean running = false;
    private static volatile double peakUsedMB = 0, maxAfterGcMB = 0, endAfterGcMB = -1;
    private static long gcAtStart = 0, gcOfRun = -1;
    private static Thread thread;
    private static final List<GarbageCollectorMXBean> COLLECTORS = ManagementFactory.getGarbageCollectorMXBeans();
    private static final long[] SEEN = new long[COLLECTORS.size()];
    private static final Set<String> HEAP_POOL_NAMES = new HashSet<>();
    private static final Set<String> EDEN_POOL_NAMES = new HashSet<>();   

    static {
        for (MemoryPoolMXBean p : ManagementFactory.getMemoryPoolMXBeans())
            if (p.getType() == MemoryType.HEAP) {
                HEAP_POOL_NAMES.add(p.getName());
                if (p.getName().contains("Eden")) EDEN_POOL_NAMES.add(p.getName());
            }
    }

    public static double usedMB() {
        Runtime rt = Runtime.getRuntime();
        return (rt.totalMemory() - rt.freeMemory()) / 1048576.0;
    }

   
    private static boolean pausesOnly(GarbageCollectorMXBean g) {
        return g.getName().contains("Concurrent");
    }

    
    private static double afterGcMB(GarbageCollectorMXBean g) {
        try {
            com.sun.management.GcInfo info = ((com.sun.management.GarbageCollectorMXBean) g).getLastGcInfo();
            if (info == null) return -1;
            long b = 0;
            for (Map.Entry<String, MemoryUsage> e : info.getMemoryUsageAfterGc().entrySet()) {
                if (!HEAP_POOL_NAMES.contains(e.getKey())) continue;
                if (EDEN_POOL_NAMES.contains(e.getKey()) && e.getValue().getUsed() > 0) return -1;
                b += e.getValue().getUsed();
            }
            return b / 1048576.0;
        } catch (Throwable t) {   
            long b = 0;
            for (MemoryPoolMXBean p : ManagementFactory.getMemoryPoolMXBeans()) {
                if (p.getType() != MemoryType.HEAP) continue;
                MemoryUsage u = p.getCollectionUsage();
                if (u != null) b += u.getUsed();
            }
            return b / 1048576.0;
        }
    }

   
    public static long gcCount() {
        long c = 0;
        for (GarbageCollectorMXBean g : COLLECTORS)
            if (!pausesOnly(g)) c += Math.max(0, g.getCollectionCount());
        return c;
    }

    private static void sample() {
        double u = usedMB();
        if (u > peakUsedMB) peakUsedMB = u;
        for (int i = 0; i < SEEN.length; i++) {
            GarbageCollectorMXBean g = COLLECTORS.get(i);
            long c = g.getCollectionCount();
            if (c > SEEN[i]) {
                SEEN[i] = c;
                if (pausesOnly(g)) continue;
                double a = afterGcMB(g);
                if (a > maxAfterGcMB) maxAfterGcMB = a;
            }
        }
    }

    public static synchronized void start() {
        for (int i = 0; i < SEEN.length; i++) SEEN[i] = Math.max(0, COLLECTORS.get(i).getCollectionCount());
        gcAtStart = gcCount();
        gcOfRun = -1;
        peakUsedMB = 0;
        maxAfterGcMB = 0;
        endAfterGcMB = -1;
        sample();
        running = true;
        thread = new Thread(new HeapSampler(), "heap-sampler");
        thread.setDaemon(true);
        thread.start();
    }

    
    public static synchronized double stop() {
        running = false;
        if (thread != null) {
            try { thread.join(1000); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
        }
        sample();
        gcOfRun = gcCount() - gcAtStart;
        System.gc();   
        endAfterGcMB = ManagementFactory.getMemoryMXBean().getHeapMemoryUsage().getUsed() / 1048576.0;
        return peakUsedMB;
    }

    
    public static double peakAfterGcMB() {
        if (collections() == 0) return peakUsedMB;
        return Math.max(maxAfterGcMB, endAfterGcMB);
    }

   
    public static long collections() {
        return gcOfRun >= 0 ? gcOfRun : gcCount() - gcAtStart;
    }

    @Override
    public void run() {
        while (running) {
            sample();
            try { Thread.sleep(PERIOD_MS); } catch (InterruptedException e) { return; }
        }
    }
}
