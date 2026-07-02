#ifndef SAGE_GRAPHS_GENUS_MULTIGENUS_H
#define SAGE_GRAPHS_GENUS_MULTIGENUS_H

int sage_multigenus_genus(int n, int m, const int *degrees,
                          const int *neighbors, int stride, int *rotation,
                          int rotation_stride, int *genus_out);

#endif
