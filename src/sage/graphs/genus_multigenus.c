#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *sage_multigenus_code = NULL;
static size_t sage_multigenus_code_len = 0;
static size_t sage_multigenus_code_cap = 0;

static int sage_multigenus_putchar(int ch)
{
    if (sage_multigenus_code_len == sage_multigenus_code_cap) {
        size_t new_cap = sage_multigenus_code_cap == 0 ? 256 : 2 * sage_multigenus_code_cap;
        unsigned char *new_code = (unsigned char *)realloc(sage_multigenus_code, new_cap);
        if (new_code == NULL) {
            return EOF;
        }
        sage_multigenus_code = new_code;
        sage_multigenus_code_cap = new_cap;
    }
    sage_multigenus_code[sage_multigenus_code_len++] = (unsigned char)ch;
    return ch;
}

#define putchar sage_multigenus_putchar
#define main sage_multigenus_program_main
#include "genus_multigenus_impl.c"
#undef main
#undef putchar

static int sage_multigenus_decode_rotation(int n, const unsigned char *code,
                                           size_t code_len, int *rotation,
                                           int rotation_stride)
{
    size_t pos = 1;
    if (code_len == 0 || code[0] != n) {
        return -3;
    }
    for (int v = 0; v < n; v++) {
        int j = 0;
        while (1) {
            if (pos >= code_len) {
                return -4;
            }
            unsigned char value = code[pos++];
            if (value == 0) {
                break;
            }
            if (j >= rotation_stride) {
                return -5;
            }
            rotation[v * rotation_stride + j++] = (int)value - 1;
        }
    }
    return 0;
}

int sage_multigenus_genus(int n, int m, const int *degrees,
                          const int *neighbors, int stride, int *rotation,
                          int rotation_stride, int *genus_out)
{
    GRAPH graph;
    ADJAZENZ adj;
    int i, j, result;

    memset(graph, 0, sizeof(graph));
    memset(adj, 0, sizeof(adj));

    if (n > knoten || 2 * m > d_kanten) {
        return -2;
    }

    graph[0][0] = (unsigned char)n;
    globalnv = n;
    globalne = m;
    write = rotation != NULL ? 1 : 0;
    filter = -1;
    filter2 = -1;
    filterl = -1;
    filterlarge = 0;
    compute_lower_bound = 1;
    reduce2 = 1;
    do_bfs = 0;
    written = 0;
    memset(good_approx, 0, sizeof(good_approx));
    sage_multigenus_code_len = 0;

    for (i = 1; i <= n; i++) {
        adj[i] = (unsigned char)degrees[i - 1];
        for (j = 0; j < degrees[i - 1]; j++) {
            graph[i][j] = (unsigned char)(neighbors[(i - 1) * stride + j] + 1);
        }
    }

    result = get_genus(graph, adj);
    if (genus_out != NULL) {
        *genus_out = result;
    }
    if (result >= 0 && rotation != NULL) {
        int decode_status = sage_multigenus_decode_rotation(n, sage_multigenus_code,
                                                            sage_multigenus_code_len,
                                                            rotation, rotation_stride);
        if (decode_status != 0) {
            return decode_status;
        }
    }
    return result;
}
