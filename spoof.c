#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include "fline.h"

#define local static

// Issue error message (all error messages go through here).
local inline void warn(const char *why) {
    fprintf(stderr, "spoof: %s\n", why);
}

// Fail and exit with error message.
local inline void fail(const char *why) {
    warn(why);
    exit(1);
}

// Assured memory allocation or reallocation.
local inline void *alloc(void *space, size_t size) {
    space = realloc(space, size);
    if (space == NULL)
        fail("out of memory");
    return space;
}

// Reverse the low n bits of x, setting the remaining bits to zero. The result
// is undefined if n is not in 1..64.
local uint64_t reverse(uint64_t x, int n) {
#if defined(__has_builtin) && __has_builtin(__builtin_bitreverse64)
    return __builtin_bitreverse64(x) >> (64 - n);
#else
    x = (((x & 0xaaaaaaaaaaaaaaaa) >> 1) |  ((x & 0x5555555555555555) << 1));
    x = (((x & 0xcccccccccccccccc) >> 2) |  ((x & 0x3333333333333333) << 2));
    x = (((x & 0xf0f0f0f0f0f0f0f0) >> 4) |  ((x & 0x0f0f0f0f0f0f0f0f) << 4));
    x = (((x & 0xff00ff00ff00ff00) >> 8) |  ((x & 0x00ff00ff00ff00ff) << 8));
    x = (((x & 0xffff0000ffff0000) >> 16) | ((x & 0x0000ffff0000ffff) << 16));
    return ((x >> 32) | (x << 32)) >> (64 - n);
#endif
}

// Types to use for CRC's and sequence lengths and offsets. In general these
// should be the largest integer types available to maximize the problems that
// can be solved. word_t could be made a smaller type if speed is paramount and
// the size of the word_t type is known to cover the CRC polynomials that will
// be presented.
typedef unsigned long long word_t;  // unsigned type for crc values
typedef unsigned long long range_t; // unsigned type for sequence offsets
#define WORDFMT "llx"               // printf, scanf format for word_t (hex)
#define RANGEFMT "llu"              // printf, scanf format for range_t
#define WORDBITS ((int)sizeof(word_t)<<3)
#define ONES(n) (((word_t)0 - 1) >> (WORDBITS - (n)))

// CRC description (with no pre or post processing)
typedef struct {
    short deg;          // number of bits in CRC
    short ref;          // if true, bit-reflected input and output
    word_t poly;        // polynomial representation (ordered per ref)
} model_t;

// Location of a bit that can be modified to get the desired CRC.
struct locus {
    range_t off;        // byte offset in sequence
    short pos;          // position in byte (0..7)
};

// Run the low eight bits in val through a crc using model.
local inline word_t crc_byte(word_t crc, unsigned val, model_t model) {
    word_t poly = model.poly;

    if (model.ref) {
        crc ^= val & 0xff;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
        crc = crc & 1 ? (crc >> 1) ^ poly : crc >> 1;
    }
    else if (model.deg < 8) {
        poly <<= 8 - model.deg;
        crc <<= 8 - model.deg;
        crc ^= val;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc = crc & 0x80 ? (crc << 1) ^ poly : crc << 1;
        crc >>= 8 - model.deg;
        crc &= ONES(model.deg);
    }
    else {
        word_t mask;

        mask = (word_t)1 << (model.deg - 1);
        crc ^= (word_t)val << (model.deg - 8);
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc = crc & mask ? (crc << 1) ^ poly : crc << 1;
        crc &= ONES(model.deg);
    }
    return crc;
}

// Multiply the GF(2) vector vec by the GF(2) matrix mat, returning the
// resulting vector. The vector is stored as bits in a word_t, and the matrix
// is similarly stored as words, where the number of words is at least enough
// to cover the position of the most significant 1 bit in the vector (so a
// dimension parameter is not needed).
local inline word_t gf2_matrix_times(const word_t *mat, word_t vec) {
    word_t sum;

    sum = 0;
    while (vec) {
        if (vec & 1)
            sum ^= *mat;
        vec >>= 1;
        mat++;
    }
    return sum;
}

// Multiply the matrix mat by itself, returning the result in square. dim is
// the dimension of the matrices, i.e., the number of bits in each word (rows),
// and the number of words (columns).
local void gf2_matrix_square(word_t *square, const word_t *mat, int dim) {
    int n;

    for (n = 0; n < dim; n++)
        square[n] = gf2_matrix_times(mat, mat[n]);
}

// Return a matrix that when multiplied by the starting crc is equivalent to
// running 2^k zero bytes through the crc calculation. The matrices are
// retained in static and allocated storage, so that they are only calculated
// once. If a new model is presented, then the previous table is cleared to
// start over. Call crc_zeros_operator(-1, model) to free the allocated storage
// and clear the table. This routine is not thread safe, and so should only be
// called from the main thread.
local const word_t *crc_zeros_operator(int k, model_t model) {
    static int have = 0;
    static model_t first;
    static word_t *power[sizeof(range_t) << 3];

    // if requested or required, release and clear the operator table
    if (k < 0 || model.deg != first.deg || model.ref != first.ref ||
                 model.poly != first.poly) {
        while (have)
            free(power[--have]);
        if (k < 0)
            return 0;
    }

    // if necessary, square up to the requested operator
    while (k >= have) {
        // first time in: create first two operators (1 and 2 zero bytes)
        if (have == 0) {
            int n;
            word_t row;

            // check and set state, allocate space for first two operators
            first = model;
            power[0] = alloc(NULL, model.deg * sizeof(word_t));
            power[1] = alloc(NULL, model.deg * sizeof(word_t));

            // generate operator for one zero bit using crc polynomial
            if (model.ref) {
                power[1][0] = model.poly;
                for (n = 1, row = 1; n < model.deg; n++, row <<= 1)
                    power[1][n] = row;
            }
            else {
                for (n = 0, row = 2; n < model.deg - 1; n++, row <<= 1)
                    power[1][n] = row;
                power[1][n] = model.poly;
            }

            // square that until we get the operator for eight zero bits
            gf2_matrix_square(power[0], power[1], model.deg);
            gf2_matrix_square(power[1], power[0], model.deg);
            gf2_matrix_square(power[0], power[1], model.deg);

            // since we have already allocated the space for it, compute the
            // operator for two zero bytes (16 zero bits)
            gf2_matrix_square(power[1], power[0], model.deg);
            have = 2;
            continue;
        }

        // square the highest operator so far and put in allocated space
        power[have] = alloc(NULL, model.deg * sizeof(word_t));
        gf2_matrix_square(power[have], power[have - 1], model.deg);
        have++;
    }

    // return the requested operator
    return power[k];
}

// Efficiently apply len zero bytes to crc, returning the resulting crc. The
// execution time of this routine is proportional to log(len). model is the crc
// description.
local word_t crc_zeros(word_t crc, range_t len, model_t model) {
    int n;

    // apply len zeros to crc
    if (crc)
        for (n = 0; len; len >>= 1, n++)
            if (len & 1)
                crc = gf2_matrix_times(crc_zeros_operator(n, model), crc);
    return crc;
}

// Compute the crc of a sparse sequence with 1's at loci[0..locs-1] (assumed to
// be sorted by offset in ascending order).
local word_t crc_sparse(const struct locus *loci, int locs, range_t len,
                        model_t model) {
    int k;              // index of loci
    unsigned val = 0;   // sequence byte consisting of one or more ones
    word_t crc = 0;     // computed crc
    range_t at = 0;     // crc calculation is at this offset so far

    // go through each location, deferring the use of val in case a byte will
    // have more than one bit set to one
    for (k = 0; k < locs; k++) {
        // assure that loci[] is sorted by offset
        assert(loci[k].off >= at);

        // if at a new offset, do crc of val if val has ones
        if (val && loci[k].off != at) {
            crc = crc_byte(crc, val, model);
            at++;
            val = 0;
        }

        // run zeros through crc up to current location
        crc = crc_zeros(crc, loci[k].off - at, model);
        at = loci[k].off;
        val |= 1 << loci[k].pos;            // add a one bit to val
    }

    // take care of leftover bits in val, if any
    if (val) {
        crc = crc_byte(crc, val, model);
        at++;
    }

    // take care of leftover zeros to run through, return result
    return crc_zeros(crc, len - at, model);
}

// Solve M x = c for x, return 0 on success, 1 on failure (singular). This
// works for rectangluar M as well (cols > rows), where a subset of the x
// values are selected that result in a non-singular square M' over that
// subset. rows is limited to the number of bits in the word_t type. cols is
// not limited (except by stack space). M is an array of cols words, where each
// word is a column, and the rows are bits in the word starting with the least
// significant bit. c is a word with rows bits stored in the same way. x[] is
// one or more words with cols bits, where the first bit is the least
// significant bin in the first word of x[]. When the bits in the first word
// run out, the next bit is in the least significant position of the next word
// in x[]. The result is returned in x[], which needs enough elements to store
// cols bits.
local int gf2_matrix_solve(word_t *x, const word_t *M, word_t c, int rows,
                           int cols) {
    int n = (cols + WORDBITS - 1) / WORDBITS;   // words to hold cols bits
    int k;              // index through columns
    int j;              // index through rows
    int i;              // index through n words holding cols bits
    word_t pos;         // word with one bit set for current row or column
    word_t a[cols];     // starting matrix, evolving to identity matrix
    word_t inv[cols][n];    // identity matrix, evolving to inverse matrix

    // copy mat to local storage and create adjoining identity matrix
    for (k = 0, j = 0, pos = 1; k < cols; k++, pos <<= 1) {
        if (pos == 0) {
            pos = 1;
            j++;
        }
        a[k] = M[k];
        for (i = 0; i < n; i++)
            inv[k][i] = i == j ? pos : 0;
    }

    // make M the identity matrix using column swaps and column subtractions
    // (exclusive-or), and perform the same operations on inv -- then the first
    // cols cols of inv will be the inverse of the selected subset of columns
    // of M
    for (j = 0, pos = 1; j < rows; j++, pos <<= 1) {
        // find a subsequent row where column j is 1, make that row j with a
        // swap if necessary -- if there isn't any such row, then there is no
        // non-singular subset of M, in which case return an error
        if ((a[j] & pos) == 0) {
            word_t tmp;

            for (k = j + 1; k < cols; k++)
                if (a[k] & pos)
                    break;
            if (k == cols)          // no such row, matrix is singular
                return 1;
            tmp = a[j], a[j] = a[k], a[k] = tmp;
            for (i = 0; i < n; i++)
                tmp = inv[j][i], inv[j][i] = inv[k][i], inv[k][i] = tmp;
        }

        // subtract row j from all the other rows with a 1 in that column
        for (k = 0; k < cols; k++)
            if (k != j && (a[k] & pos) != 0) {
                a[k] ^= a[j];
                for (i = 0; i < n; i++)
                    inv[k][i] ^= inv[j][i];
            }
    }

    // multiply inverse by c to get result x
    assert(c <= ONES(rows));
    for (i = 0; i < n; i++)
        x[i] = 0;
    for (j = 0; c; c >>= 1, j++)
        if (c & 1) {
            for (i = 0; i < n; i++)
                x[i] ^= inv[j][i];
        }
    return 0;
}

// Solve for the set of loci and the desired crc. Return the number of
// locations to invert, or -1 if there is no solution. The locations to invert
// are moved to the beginning of loci. If there is no solution, loci is not
// modified.
local int crc_solve(struct locus *loci, int locs, range_t len, word_t want,
                    model_t model) {
    int n, k, i;
    word_t p, sol[(locs + WORDBITS - 1) / WORDBITS];
    word_t mat[locs];

    // protect against improper input that could cause array overruns
    assert(locs >= model.deg);
    assert(want <= ONES(model.deg));

    // for each bit position, calculate the crc of the sequence of len zero
    // bytes except for a single 1 bit at that bit position
    for (k = 0; k < locs; k++)
        mat[k] = crc_sparse(loci + k, 1, len, model);

    // solve mat . sol = want for sol (return if all square subsets of mat are
    // singular)
    k = gf2_matrix_solve(sol, mat, want, model.deg, locs);
    if (k)
        return -1;

    // move the locations to invert up to the front of loci
    for (k = 0, n = 0, i = 0, p = 1; k < locs; k++, p <<= 1) {
        if (p == 0) {
            p = 1;
            i++;
        }
        if (sol[i] & p)
            loci[n++] = loci[k];
    }
    return n;
}

// Comparison function for sorting loci, used by qsort().
local int locus_order(const void *a, const void *b) {
    const struct locus *p = a, *q = b;

    if (p->off != q->off)
        return p->off < q->off ? -1 : 1;
    return p->pos < q->pos ? -1 : (p->pos > q->pos ? 1 : 0);
}

// Return the number of decimal digits in the unsigned number n.
local inline int decimal_digits(range_t n) {
    int i;

    i = 0;
    do {
        n /= 10;
        i++;
    } while (n);
    return i;
}

#ifndef NOMAIN  // for testing

// Return a null-terminated line of input from state, stripping any comments
// and skipping blank lines. Also replace any nulls with spaces so the line can
// be terminated by a null. A comment starts where the first hash (#) character
// appears anywhere in the line, and ends at the end of the line. A returned
// empty line indicates EOF or error.
local inline char *getinput(fline_t *state) {
    size_t len;
    int ch;
    char *line, *loc;

    do {
        line = fline(state, &len);
        if (line == NULL)
            fail("out of memory");
        if (len == 0)
            break;
        loc = memchr(line, '#', len);
        if (loc != NULL)
            len = loc - line;
        loc = line;
        while ((loc = memchr(loc, 0, len - (loc - line))) != NULL)
            *loc++ = ' ';
        while (len && ((ch = line[len - 1]) == ' ' || ch == '\t' ||
                       ch == '\n' || ch == '\r'))
            len--;
    } while (len == 0);
    line[len] = 0;
    return line;
}

// Read sequence length, bit positions, and desired crc difference from stdin.
// Compute and display the solution, which is a subset of the provided bit
// positions to invert in the sequence.
int main(void) {
    int k;                      // counter for locations, bits
    word_t crc;                 // calculated crc to check solution
    int ret;                    // general function return value
    FILE *in = stdin;           // input file
    fline_t *state;             // state for fline()
    model_t model;              // CRC model
    word_t want;                // desired crc
    range_t len;                // length of sequence in bytes
    struct locus *loci;         // bit locations
    range_t off;                // offset of bit to potentially flip
    int pos;                    // position of bit to potentially flip
    int locs;                   // number of bit locations to look at
    int flips;                  // number of bit locations to invert
    char *line;                 // input line
    int n;                      // position from sscanf()

    // set up input
    state = fline_start(in);
    if (state == NULL)
        fail("out of memory");

    // read crc description
    ret = sscanf(getinput(state), " %hd %" WORDFMT " %hd",
                 &model.deg, &model.poly, &model.ref);
    if (ret == 3 && model.deg > WORDBITS)
        fail("CRC too long for crc integer type spoof was compiled with");
    if (ret < 3 || model.deg < 1 || model.ref < 0 || model.ref > 1 ||
                   model.poly > ONES(model.deg) || (model.poly & 1) == 0)
        fail("invalid CRC description");
    if (model.ref)
        model.poly = reverse(model.poly, model.deg);

    // read desired crc difference and number of bytes in the sequence
    ret = sscanf(getinput(state), " %" WORDFMT " %" RANGEFMT,
                 &want, &len);
    if (ret < 1 || want > ONES(model.deg))
        fail("invalid target CRC");
    if (ret < 2 || len < (range_t)((model.deg + 7) >> 3))
        fail("invalid sequence length (must be at least length of CRC)");

    // read bit locations
    k = model.deg << 1;
    loci = alloc(NULL, k * sizeof(struct locus));
    locs = 0;
    while ((ret = sscanf(line = getinput(state), " %" RANGEFMT "%n",
                         &off, &n)) > 0) {
        if (off >= len)
            fail("invalid bit location offset");
        line += n;
        while ((ret = sscanf(line, "%d%n", &pos, &n)) > 0) {
            line += n;
            if (pos < 0 || pos > 7)
                fail("invalid bit position");
            if (locs == k) {
                k <<= 1;
                loci = alloc(loci, k * sizeof(struct locus));
            }
            loci[locs].off = off;
            loci[locs].pos = pos;
            locs++;
        }
    }
    fline_end(state);
    if (locs < model.deg)
        fail("need at least n bit locations for an n-bit CRC");
    loci = alloc(loci, locs * sizeof(struct locus));

    // solve for the values of the given bit locations to get want
    flips = crc_solve(loci, locs, len, want, model);
    if (flips == -1)
        fail("no solution -- try more or different bit locations");

    // check the crc of a sequence with ones at the given locations -- sort the
    // locations by offset first, since crc_sparse() requires that
    qsort(loci, flips, sizeof(struct locus), locus_order);
    crc = crc_sparse(loci, flips, len, model);
    if (want != crc)
        fail("internal algorithm error");

    // output what bits to invert to get the desired crc
    if (flips) {
        puts("invert these bits in the sequence:");
        ret = decimal_digits(loci[flips - 1].off);
        if (ret < 6)
            ret = 6;
        printf("%*s bit\n", ret, "offset");
        for (k = 0; k < flips; k++)
            printf("%*" RANGEFMT " %d\n", ret, loci[k].off, loci[k].pos);
    }
    else
        puts("no need to invert any bits in sequence");

    // clean up and return success
    crc_zeros_operator(-1, model);
    free(loci);
    return 0;
}

#endif
