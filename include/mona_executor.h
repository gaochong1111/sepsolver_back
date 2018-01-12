#ifndef MONA_EXECUTOR_H
#define MONA_EXECUTOR_H
#include <iostream>
#include <map>
#include <algorithm>

class mona_executor {
private:
        std::string m_name;
        std::string m_args;

private:
        void get_minus_val(std::string& value);
public:
        mona_executor(){}
        void set_name(std::string name) {m_name = name;}
        void set_args(std::string args) {m_args = args;}
        bool execute(std::map<std::string, std::string>& model);
        bool parse_model(std::string& output,  std::map<std::string, std::string>& model);

};


#endif /* MONA_EXECUTOR_H */
