#include "machine.h"

#define BUF_SZ 256

char buffer[BUF_SZ];

char *myread(void)
{
    int i;
    char *ret = NULL;
    for (i = 0; i < BUF_SZ; i++)
        buffer[i] = 0;
    void *p = fgets(buffer, BUF_SZ, stdin);
    ret = malloc(BUF_SZ * sizeof(*buffer) + 1);
    for (i = 0; i < BUF_SZ; i++)
    {
        if (buffer[i] != '\0')
            ret[i] = buffer[i];
        else
            break;
    }
    buffer[i] = '\0';
    return ret;
}
