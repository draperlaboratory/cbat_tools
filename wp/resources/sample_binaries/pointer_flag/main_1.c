int f(){
    return 1;
}
// Type your code here, or load an example.
int deref(int *num1) {
    int num2 = f();
    if(*num1 >= num2){
        return -1;
    }
    return 0;
}

int main(int argc, char** argv){
        return 0;
}
