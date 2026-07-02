#ifndef SAGE_GRAPHS_GENUS_PAGE_H
#define SAGE_GRAPHS_GENUS_PAGE_H

int sage_page_genus(int n, int m, int degree, const int *degrees,
                    const int *neighbors, int stride, int *rotation,
                    int rotation_stride, int *genus_out);

#endif
