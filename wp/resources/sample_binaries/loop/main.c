#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

int main(int argc, char** argv){
        int counter = 0;
	for(int i = 0; i <= argc; i++){
	        counter += 1;
	}
	if(counter == 1){
		assert(0);
	}
	return 0;
}
