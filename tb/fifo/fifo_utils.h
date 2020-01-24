
#ifndef FIFO_UTILS_H_
#define FIFO_UTILS_H_

typedef enum {ERROR, WARN, NOTE} PrintLevel;

void modelPrint(PrintLevel level,
                unsigned int t, // time
                char * modelinfo,
                char const * msg,
                ...);

#endif // FIFO_UTILS_H_

