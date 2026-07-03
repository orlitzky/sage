/*
 * Sage wrapper for the PAGE graph genus algorithm.
 *
 * AUTHORS:
 *
 * - Alexander Metzger and Austin Ulrigg (2026): PAGE algorithm
 * - Alexander Metzger (2026): Sage C wrapper
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *                  https://www.gnu.org/licenses/
 */

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "genus_page.h"

#include "genus_page_impl.c"

static int sage_page_parse_output(FILE *out, int n, int degree, const int *degrees,
                                  const int *neighbors, int stride, int *rotation,
                                  int rotation_stride, int *genus_out)
{
    char line[65536];
    int *next = NULL;
    int saw_cycle = 0;
    int genus = -1;

    rewind(out);
    next = (int *)malloc((size_t)n * degree * sizeof(int));
    if (next == NULL) {
        return -3;
    }
    for (int i = 0; i < n * degree; i++) {
        next[i] = -1;
    }

    while (fgets(line, sizeof(line), out) != NULL) {
        int parsed_genus;
        char *p;
        if (sscanf(line, "Genus found: %d", &parsed_genus) == 1) {
            genus = parsed_genus;
            continue;
        }
        p = strstr(line, "(genus ");
        if (p != NULL && sscanf(p, "(genus %d", &parsed_genus) == 1) {
            genus = parsed_genus;
            continue;
        }

        int values[8192];
        int count = 0;
        p = line;
        while (*p != '\0') {
            char *end = NULL;
            long value;
            while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') {
                p++;
            }
            if (*p == '\0') {
                break;
            }
            errno = 0;
            value = strtol(p, &end, 10);
            if (end == p || errno != 0 || value < 0 || value >= n || count >= 8192) {
                count = 0;
                break;
            }
            values[count++] = (int)value;
            p = end;
        }
        if (count < 4 || values[0] != values[count - 1]) {
            continue;
        }
        saw_cycle = 1;
        count--;
        for (int i = 0; i < count; i++) {
            int center = values[i];
            int prev = values[(i + count - 1) % count];
            int succ = values[(i + 1) % count];
            int slot = -1;
            for (int j = 0; j < degrees[center]; j++) {
                if (neighbors[center * stride + j] == prev) {
                    slot = j;
                    break;
                }
            }
            if (slot < 0) {
                free(next);
                return -4;
            }
            next[center * degree + slot] = succ;
        }
    }

    if (genus_out != NULL) {
        *genus_out = genus;
    }
    if (rotation != NULL && saw_cycle) {
        for (int v = 0; v < n; v++) {
            if (degrees[v] == 0) {
                continue;
            }
            int first = neighbors[v * stride];
            int current = first;
            for (int k = 0; k < degrees[v]; k++) {
                int slot = -1;
                rotation[v * rotation_stride + k] = current;
                for (int j = 0; j < degrees[v]; j++) {
                    if (neighbors[v * stride + j] == current) {
                        slot = j;
                        break;
                    }
                }
                if (slot < 0 || next[v * degree + slot] < 0) {
                    free(next);
                    return -5;
                }
                current = next[v * degree + slot];
            }
            if (current != first) {
                free(next);
                return -6;
            }
        }
    }
    free(next);
    return genus >= 0 ? genus : -7;
}

int sage_page_genus(int n, int m, int degree, const int *degrees,
                    const int *neighbors, int stride, int *rotation,
                    int rotation_stride, int *genus_out)
{
    char template_name[] = "/tmp/sage-page-XXXXXX";
    int fd = mkstemp(template_name);
    FILE *input = NULL;
    FILE *output = NULL;
    int status;
    int result;

    if (fd < 0) {
        return -1;
    }
    input = fdopen(fd, "w");
    if (input == NULL) {
        close(fd);
        unlink(template_name);
        return -1;
    }
    fprintf(input, "%d %d\n", n, m);
    for (int v = 0; v < n; v++) {
        for (int j = 0; j < degree; j++) {
            int value = j < degrees[v] ? neighbors[v * stride + j] : MAX_VERTICES;
            fprintf(input, "%d%s", value, j + 1 == degree ? "\n" : " ");
        }
    }
    fclose(input);

    output = tmpfile();
    if (output == NULL) {
        unlink(template_name);
        return -2;
    }
    status = sage_page_run_file(template_name, degree, 0, 0, output);
    unlink(template_name);
    if (status != 0) {
        fclose(output);
        return -8;
    }
    result = sage_page_parse_output(output, n, degree, degrees, neighbors, stride,
                                    rotation, rotation_stride, genus_out);
    fclose(output);
    return result;
}
