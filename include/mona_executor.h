#ifndef MONA_EXECUTOR_H
#define MONA_EXECUTOR_H
#include <iostream>

class mona_executor {
private:
        std::string m_name;
        std::string m_args;
public:
        mona_executor(){}
        void set_name(std::string name) {m_name = name;}
        void set_args(std::string args) {m_args = args;}
        std::string execute();

};


#endif /* MONA_EXECUTOR_H */
