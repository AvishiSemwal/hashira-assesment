import java.io.*;
import java.math.BigInteger;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Hashira Placements – Polynomial Interpolation (No Python)
 * - Reads JSON from STDIN (specific input shape per prompt)
 * - Converts mixed-radix y-values to BigInteger
 * - Uses exact BigRational arithmetic
 * - Builds polynomial via Newton divided differences, then expands to standard basis
 * - Verifies against all points
 *
 * Compile: javac Main.java
 * Run:     java Main < testcase.json
 */
public class Main {

    /* ----------------------- Exact Rational ----------------------- */
    static final class BigRational {
        final BigInteger n; // numerator
        final BigInteger d; // denominator > 0

        BigRational(BigInteger n, BigInteger d) {
            if (d.signum() == 0) throw new ArithmeticException("denominator is zero");
            if (d.signum() < 0) { n = n.negate(); d = d.negate(); }
            BigInteger g = n.gcd(d);
            this.n = n.divide(g);
            this.d = d.divide(g);
        }
        static BigRational of(long v) { return new BigRational(BigInteger.valueOf(v), BigInteger.ONE); }
        static BigRational of(BigInteger v) { return new BigRational(v, BigInteger.ONE); }

        BigRational add(BigRational o) {
            return new BigRational(n.multiply(o.d).add(o.n.multiply(d)), d.multiply(o.d));
        }
        BigRational sub(BigRational o) {
            return new BigRational(n.multiply(o.d).subtract(o.n.multiply(d)), d.multiply(o.d));
        }
        BigRational mul(BigRational o) {
            return new BigRational(n.multiply(o.n), d.multiply(o.d));
        }
        BigRational div(BigRational o) {
            if (o.n.signum() == 0) throw new ArithmeticException("divide by zero");
            return new BigRational(n.multiply(o.d), d.multiply(o.n));
        }
        public String toString() {
            return d.equals(BigInteger.ONE) ? n.toString() : (n + "/" + d);
        }
        public boolean isInteger() { return d.equals(BigInteger.ONE); }
    }

    /* -------------------------- Polynomial ------------------------ */
    // Coeffs in ascending powers: c[0] + c[1] x + ... + c[m] x^m
    static final class Poly {
        ArrayList<BigRational> c = new ArrayList<>();

        Poly() {}
        static Poly constant(BigRational k) { Poly p = new Poly(); p.c.add(k); return p; }

        int deg() { return c.size() - 1; }

        BigRational coeff(int i) { return i < c.size() ? c.get(i) : BigRational.of(0); }

        void trim() {
            int i = c.size() - 1;
            while (i > 0 && c.get(i).n.signum() == 0) i--;
            if (i + 1 < c.size()) c.subList(i + 1, c.size()).clear();
        }

        Poly add(Poly other) {
            Poly r = new Poly();
            int n = Math.max(this.c.size(), other.c.size());
            for (int i = 0; i < n; i++) {
                r.c.add(this.coeff(i).add(other.coeff(i)));
            }
            r.trim();
            return r;
        }

        Poly scale(BigRational k) {
            Poly r = new Poly();
            for (BigRational ci : c) r.c.add(ci.mul(k));
            r.trim();
            return r;
        }

        // Multiply by (x - a)
        Poly timesXminus(BigRational a) {
            Poly r = new Poly();
            int n = c.size();
            // shift
            r.c.add(BigRational.of(0)); // for x*c0
            for (int i = 0; i < n; i++) r.c.add(BigRational.of(0));
            for (int i = 0; i < n; i++) {
                // x * c_i
                r.c.set(i + 1, r.c.get(i + 1).add(c.get(i)));
                // -a * c_i
                r.c.set(i, r.c.get(i).sub(c.get(i).mul(a)));
            }
            r.trim();
            return r;
        }

        BigInteger evalInt(int x) {
            // Evaluate in Z using Horner with rationals -> returns numerator/denominator; but
            // here we only use for verification where y is integer; do exact rational and assert integer.
            BigRational r = BigRational.of(0);
            for (int i = c.size() - 1; i >= 0; i--) {
                r = r.mul(BigRational.of(x)).add(c.get(i));
            }
            if (!r.isInteger()) throw new RuntimeException("Evaluation not integer at x=" + x + ": " + r);
            return r.n;
        }

        public String toString() {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < c.size(); i++) {
                sb.append("a").append(i).append(" = ").append(c.get(i)).append("\n");
            }
            return sb.toString();
        }
    }

    /* -------------------------- JSON Parse ------------------------ */
    static final class Point { final int x; final BigInteger y; Point(int x, BigInteger y){ this.x=x; this.y=y; } }

    // Extracts keys.n and keys.k
    static int[] parseNK(String s) {
        Pattern p = Pattern.compile("\"keys\"\\s*:\\s*\\{[^}]*\"n\"\\s*:\\s*(\\d+)\\s*,\\s*\"k\"\\s*:\\s*(\\d+)", Pattern.DOTALL);
        Matcher m = p.matcher(s);
        if (!m.find()) throw new RuntimeException("Failed to parse keys.n / keys.k");
        return new int[]{ Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)) };
    }

    // Extract "x": { "base": "b", "value": "v" }  (x is an integer key)
    static List<Point> parsePoints(String s) {
        Pattern p = Pattern.compile("\"(\\d+)\"\\s*:\\s*\\{\\s*\"base\"\\s*:\\s*\"(\\d+)\"\\s*,\\s*\"value\"\\s*:\\s*\"([0-9A-Za-z]+)\"\\s*\\}");
        Matcher m = p.matcher(s);
        ArrayList<Point> pts = new ArrayList<>();
        while (m.find()) {
            int x = Integer.parseInt(m.group(1));
            int base = Integer.parseInt(m.group(2));
            String val = m.group(3);
            if (base < 2 || base > 36) throw new RuntimeException("Unsupported base: " + base);
            BigInteger y = new BigInteger(val, base);
            pts.add(new Point(x, y));
        }
        return pts;
    }

    /* ------------------ Newton Interpolation (Q) ------------------ */
    static Poly interpolateNewton(List<Point> pts, int k) {
        // Sort by x and pick first k distinct x
        pts.sort(Comparator.comparingInt(p -> p.x));
        ArrayList<Point> used = new ArrayList<>();
        Integer lastX = null;
        for (Point p : pts) {
            if (lastX == null || p.x != lastX) {
                used.add(p);
                lastX = p.x;
                if (used.size() == k) break;
            }
        }
        if (used.size() < k) throw new RuntimeException("Not enough distinct x to interpolate");

        int n = k;
        BigRational[][] dd = new BigRational[n][n]; // divided differences
        for (int i = 0; i < n; i++) dd[i][0] = BigRational.of(used.get(i).y);
        for (int j = 1; j < n; j++) {
            for (int i = 0; i < n - j; i++) {
                BigRational num = dd[i + 1][j - 1].sub(dd[i][j - 1]);
                BigRational den = BigRational.of(used.get(i + j).x - used.get(i).x);
                dd[i][j] = num.div(den);
            }
        }

        // Build polynomial in standard basis by expanding Newton form
        Poly poly = Poly.constant(BigRational.of(0));
        Poly term = Poly.constant(BigRational.of(1)); // product_{t < i} (x - x_t)
        for (int i = 0; i < n; i++) {
            poly = poly.add(term.scale(dd[0][i]));
            if (i < n - 1) {
                term = term.timesXminus(BigRational.of(used.get(i).x));
            }
        }
        return poly;
    }

    /* ----------------------------- IO ----------------------------- */
    static String readAll(InputStream in) throws IOException {
        ByteArrayOutputStream bos = new ByteArrayOutputStream();
        byte[] buf = new byte[1<<16];
        for (int r; (r = in.read(buf)) != -1; ) bos.write(buf, 0, r);
        return bos.toString("UTF-8");
    }

    /* ----------------------------- Main --------------------------- */
    public static void main(String[] args) throws Exception {
        String json = readAll(System.in).trim();
        int[] nk = parseNK(json);
        int n = nk[0], k = nk[1];
        if (k < 1) throw new RuntimeException("k must be >= 1");
        List<Point> pts = parsePoints(json);
        if (pts.size() < k) throw new RuntimeException("Have " + pts.size() + " points, need k=" + k);

        Poly poly = interpolateNewton(pts, k);

        // Print degree and coefficients (a0..am)
        poly.trim();
        int m = poly.deg();
        System.out.println("Degree m = " + m);
        System.out.println("Coefficients (a0..a" + m + "):");
        for (int i = 0; i < poly.c.size(); i++) {
            System.out.println("a" + i + " = " + poly.c.get(i));
        }

        // Optional: verify against ALL provided points
        boolean ok = true;
        for (Point p : pts) {
            BigInteger yi = poly.evalInt(p.x);
            if (!yi.equals(p.y)) {
                ok = false;
                System.out.println("VERIFY MISMATCH at x=" + p.x + ": expected " + p.y + ", got " + yi);
            }
        }
        System.out.println(ok ? "VERIFY: all provided points match ✅" : "VERIFY: mismatches found ❌");
    }
}
