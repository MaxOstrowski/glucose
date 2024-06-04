#include "utils/Options.h"
#include "utils/ParseUtils.h"


namespace Glucose {

bool DoubleOption::parse(const char* str){
    const char* span = str; 

    if (!match(span, "-") || !match(span, name) || !match(span, "="))
        return false;

    char*  end;
    double tmp = strtod(span, &end);

    if (end == NULL) 
        return false;
    else if (tmp >= range.end && (!range.end_inclusive || tmp != range.end)){
        fprintf(stderr, "ERROR! value <%s> is too large for option \"%s\".\n", span, name);
        exit(1);
    }else if (tmp <= range.begin && (!range.begin_inclusive || tmp != range.begin)){
        fprintf(stderr, "ERROR! value <%s> is too small for option \"%s\".\n", span, name);
        exit(1); }

    value = tmp;
    // fprintf(stderr, "READ VALUE: %g\n", value);

    return true;
}


 bool IntOption::parse(const char* str){
    const char* span = str; 

    if (!match(span, "-") || !match(span, name) || !match(span, "="))
        return false;

    char*   end;
    int32_t tmp = strtol(span, &end, 10);

    if (end == NULL) 
        return false;
    else if (tmp > range.end){
        fprintf(stderr, "ERROR! value <%s> is too large for option \"%s\".\n", span, name);
        exit(1);
    }else if (tmp < range.begin){
        fprintf(stderr, "ERROR! value <%s> is too small for option \"%s\".\n", span, name);
        exit(1); }

    value = tmp;

    return true;
}

#ifndef _MSC_VER
bool Int64Option::parse(const char* str){
    const char* span = str; 

    if (!match(span, "-") || !match(span, name) || !match(span, "="))
        return false;

    char*   end;
    int64_t tmp = strtoll(span, &end, 10);

    if (end == NULL) 
        return false;
    else if (tmp > range.end){
        fprintf(stderr, "ERROR! value <%s> is too large for option \"%s\".\n", span, name);
        exit(1);
    }else if (tmp < range.begin){
        fprintf(stderr, "ERROR! value <%s> is too small for option \"%s\".\n", span, name);
        exit(1); }

    value = tmp;

    return true;
}
#endif


bool StringOption::parse(const char* str){
    const char* span = str; 

    if (!match(span, "-") || !match(span, name) || !match(span, "="))
        return false;

    value = span;
    return true;
}


bool BoolOption::parse(const char* str){
    const char* span = str; 
    
    if (match(span, "-")){
        bool b = !match(span, "no-");

        if (strcmp(span, name) == 0){
            value = b;
            return true; }
    }

    return false;
}

}