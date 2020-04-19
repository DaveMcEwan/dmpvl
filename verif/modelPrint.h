
#ifndef MODELPRINT_H_
#define MODELPRINT_H_

typedef enum {ERROR, WARN, NOTE} PrintLevel;

void modelPrint(PrintLevel level,
                unsigned int t, // time
                char * modelinfo,
                char const * msg,
                ...);

#endif // MODELPRINT_H_

