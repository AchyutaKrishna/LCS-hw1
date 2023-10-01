// function return values:
// 1 - Proceed with recursive call to DPLL normally
// 2 - the current assignment satisfies the formula
// 3 - DPLL is completed
// 4 - the current assignment does not satisfy the formula

#include<bits/stdc++.h>
using namespace std;

struct Form{
    map<int,int> propsValue;
    map<int,int> propsCount;
    vector<vector<int>> clauses;
};

clock_t tStart;
Form form;
int nprop, nclause;
int cnt = 0;

void getInput(string filename){

    string myText;
    ifstream MyReadFile(filename);

    while(getline (MyReadFile, myText)){
        istringstream iss1(myText);
        vector<string> tokens(istream_iterator<string>{iss1}, istream_iterator<string>());
        while(tokens[0] != "c" && tokens[0] != "p"){ // handle BOM UTF-8 markers added in the beginning by ifstream
            tokens[0].erase(tokens[0].begin());
        }
        if(tokens[0] != "c") {
            nprop = stoi(tokens[2]);
            nclause = stoi(tokens[3]);
            break;
        }
    }
    
    form.clauses.resize(nclause);
    int c = 0;
    while (getline (MyReadFile, myText)) {
        istringstream iss2(myText);
        vector<string> cl(istream_iterator<string>{iss2}, istream_iterator<string>());
        for(int j = 0; j < cl.size(); j++){
            if(cl[j] != "0") form.clauses[c].push_back(stoi(cl[j])); // insert propositions to clauses
        }
        c++;
    }

    MyReadFile.close();

    for(int i = 0; i < nclause; i++){
        for(int j = 0; j < form.clauses[i].size(); j++){
            int tmp = form.clauses[i][j];
            if(form.propsValue.find(abs(tmp)) == form.propsValue.end()){
                if(form.clauses[i].size() == 3) form.propsCount[abs(tmp)] = 1; // add to count of number of times the proposition has occured in clauses of size 2
                else form.propsCount[abs(tmp)] = 0;  
                form.propsValue[abs(tmp)] = -1; // create an entry i the map to store the proposition's value, initialize it to -1
            }
            else{
                if(form.clauses[i].size() == 3) form.propsCount[abs(tmp)]++;  // add to count of number of times the proposition has occured in clauses of size 2
            }
        }
    }
}

int applyPropValue(Form &f, int propToApply){  // apply the value of a proposition to the clauses
    int valueToApply = f.propsValue[propToApply];
    for(int i = 0; i < f.clauses.size(); i++){
        for(int j = 0; j < f.clauses[i].size(); j++){
            if(abs(f.clauses[i][j]) == propToApply){
                if((f.clauses[i][j] > 0 && valueToApply == 1) || (f.clauses[i][j] < 0 && valueToApply == 0)) { // if T for a positive or F for a negative prop - the prop assignment becomes true, hence whole clause becomes true, hence remove clause
                    f.clauses.erase(f.clauses.begin() + i); // remove the clause from the list
                    i--;
                    if(f.clauses.size() == 0) return 2;
                    break;
                }
            
                else if((f.clauses[i][j] > 0 && valueToApply == 0) || (f.clauses[i][j] < 0 && valueToApply == 1)) { // if F for a positive or T for a negative prop - remove prop from the clause
                    f.clauses[i].erase(f.clauses[i].begin() + j);
                    j--;
                    //cout<<"C"<<" "<<f.clauses[i].size();
                    if (f.clauses[i].size() == 0) {
                        //cout<<"D";
                        return 4;
                    }
                }
            }
        }
    }
    return 1;
}

int unitPropagate(Form &f){ // perform unit propogation
    if(f.clauses.size() == 0) return 2;
    else {
        bool flag = true;
        while(flag){    // loop until a unit clause is found
            flag = false;
            for(int i = 0; i < f.clauses.size(); i++){
                if(f.clauses[i].size() == 1){
                    flag = true;
                    f.propsValue[abs(f.clauses[i][0])] = (f.clauses[i][0] > 0 ? 1:0); // assign value to the prop in the unit clause
                    f.propsCount[abs(f.clauses[i][0])] = -1; // set the count value of the prop to -1
                    int prev = f.clauses.size();
                    int res = applyPropValue(f, abs(f.clauses[i][0])); // apply the prop value
                    if(f.clauses.size() < prev) i--;
                    if(res == 2 || res == 4) return res;
                    break;
                }
                else if(f.clauses[i].size() == 0) return 4;
            }
        }
    }

    return 1;
}

tuple<int, int> identifyNextProp(Form f){ // Heuristic function - 2 clause heuristic
    int prop = -1, maxCount = 0;
    map<int,int> curcnt;
    
    for(int i = 0; i < f.clauses.size(); i++){
        if(f.clauses[i].size() == 2){
           for(int j = 0; j < f.clauses[i].size(); j++){
                int tmp = f.clauses[i][j];
                curcnt[abs(tmp)]++;  // add to count of number of times the proposition has occured in clauses of size 2
            }     
        }
    }

    for(auto p: curcnt){
        if(p.second >= maxCount){
            maxCount = maxCount;
            prop = p.first;
        }
    }
    if(curcnt.empty()) {
        for(auto p: f.propsCount){
        if(p.second >= 0){
            prop = p.first;
            break;
        }
    }
    }
    int val = 0;
    return make_tuple(prop, val);
}

int DPLL(Form f){
    cnt++;
    if(((long double)(clock() - tStart)/CLOCKS_PER_SEC) > 300) return 5;
    int res = unitPropagate(f); // initially unit propagate
    if(res == 2){
        form = f;
        return 3;
    }
    else if(res == 4) {
        return 1;
    }

    int prop, val;
    tie(prop, val) = identifyNextProp(f); // call heuristic function
    for(int i = 0; i < 2; i++){  // looping twice to try both possible values of prop if required 
        Form f1 = f;
        f1.propsValue[prop] = (val+i)%2; // set the value returned by the heuristic in the 1st iteration, set the opposite in the 2nd iteration
        f1.propsCount[prop] = -1;
        int res = applyPropValue(f1,prop);
        if(res == 2) {
            form = f1;
            return 3;
        }
        else if(res == 4) continue;
        int dpllResult = DPLL(f1);
        if(dpllResult == 3) return dpllResult;
        if(dpllResult == 5) return dpllResult;
    }

    return 1;
}

int main(){
    vector<int> t = {360};
    for(int i = 0; i < t.size(); i++){
    int c = 100;
    int nvs = 100, lvs = t[i];
    string f1 = "formulas/f" + to_string(nvs) + "_" + to_string(lvs) + "/res3c.txt";
    ofstream MyFile(f1);
    vector<int> countv;
    vector<long double> timev;
    vector<int> unsatv;
    while(c--){
        string filename = "formulas/f" + to_string(nvs) + "_" + to_string(lvs) + "/form" + to_string(100-c) + ".txt";
        getInput(filename);
        tStart = clock();
        int res = DPLL(form);
        long double tm = (long double)(clock() - tStart)/CLOCKS_PER_SEC;
        if(res == 5) cout<<"stop";
        cout<<tm<<"\n";
        countv.push_back(cnt);
        timev.push_back(tm);
        cnt = 0;
        if(res == 1) unsatv.push_back(100-c);
    }

    for(int i = 0; i < countv.size(); i++) MyFile<<countv[i]<<", ";
    MyFile<<endl<<"Time taken"<<endl;
    for(int i = 0; i < timev.size(); i++) {
        MyFile<<timev[i]<<", ";
    }
    MyFile<<endl<<"Index of UNSAT forms:"<<endl;
    for(int i = 0; i < unsatv.size(); i++) MyFile<<unsatv[i]<<", ";
    MyFile.close();
    
    }
    return 0;
}