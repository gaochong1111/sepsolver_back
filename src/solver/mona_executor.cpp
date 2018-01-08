#include "mona_executor.h"

std::string mona_executor::execute() {
        std::string cmd = "mona ";
        cmd.append(m_args);
        cmd.append(" ").append(m_name);
        FILE  *fp=popen(cmd.c_str(), "r");
        std::string output;
        char c;
        while((c=fgetc(fp)) != EOF) {
                output.append(1, c);
        }
        pclose(fp);
        return output;
}
