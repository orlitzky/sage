/*
 * C declarations for the Sage PAGE graph genus wrapper.
 *
 * AUTHORS:
 *
 * - Alexander Metzger (2026): Sage C wrapper
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *                  https://www.gnu.org/licenses/
 */

#ifndef SAGE_GRAPHS_GENUS_PAGE_H
#define SAGE_GRAPHS_GENUS_PAGE_H

int sage_page_genus(int n, int m, int degree, const int *degrees,
                    const int *neighbors, int stride, int *rotation,
                    int rotation_stride, int *genus_out);

#endif
