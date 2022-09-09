class If {

    void deadLoop() {
        int x = 1;
        int y = 0;
        int z = 100;
        if (x < y)
            use(1);
        else
            use(2);
        dead(); // unreachable branch
    }

    void dead() {
    }

    void use(int n) {
    }
}
