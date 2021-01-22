#include <assert.h>
#include <stdlib.h>

#define STRING_MAX 10

void gotoExample()
{
    char *string1, *string2, *string3, *string4, *string5;

    if ( !(string1 = (char*) calloc(STRING_MAX, sizeof(char))) )
        goto gotoExample_string1;
    if ( !(string2 = (char*) calloc(STRING_MAX, sizeof(char))) )
        goto gotoExample_string2;
    if ( !(string3 = (char*) calloc(STRING_MAX, sizeof(char))) )
        goto gotoExample_string3;
    if ( !(string4 = (char*) calloc(STRING_MAX, sizeof(char))) )
        goto gotoExample_string4;
    if ( !(string5 = (char*) calloc(STRING_MAX, sizeof(char))) )
        goto gotoExample_string5;

    //important code goes here
    assert(string1 && string2 && string3 && string4 && string5);

gotoExample_string5:
    free(string5);
gotoExample_string4:
    free(string4);
gotoExample_string3:
    free(string3);
gotoExample_string2:
    free(string2);
gotoExample_string1:
    free(string1);
}

void nestedIfExample()
{
    char *string1, *string2, *string3, *string4, *string5;

    if (string1 = (char*) calloc(STRING_MAX, sizeof(char)))
    {
        if (string2 = (char*) calloc(STRING_MAX, sizeof(char)))
        {
            if (string3 = (char*) calloc(STRING_MAX, sizeof(char)))
            {
                if (string4 = (char*) calloc(STRING_MAX, sizeof(char)))
                {
                    if (string5 = (char*) calloc(STRING_MAX, sizeof(char)))
                    {
                        //important code here
                      assert(string1
                             && string2
                             && string3
                             && string4
                             && string5);
                        free(string5);
                    }
                    free(string4);
                }
                free(string3);
            }
            free(string2);
        }
        free(string1);
    }
}


int main(int argc, char* argv[])
{
    nestedIfExample();
    gotoExample();
    return 0;
}
