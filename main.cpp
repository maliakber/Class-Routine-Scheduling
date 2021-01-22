#include<stdio.h>
#include<string.h>
#include<math.h>
#include<stdlib.h>
#include<vector>
#include<algorithm>
#include<iostream>
#include<set>
#include<map>
#include<list>
#include<string>
#include<stack>
#include<queue>
#include<sstream>
#include<fstream>
#include<time.h>
using namespace std;

// Template By @li_@kber
typedef long long int ll;
typedef unsigned long long int ull;
const double pi=acos(-1.0);
int parent[100001];
int inf=100000000;
//int row[]={1,0,-1,0};int col[]={0,1,0,-1}; //4 Direction
//int row[]={1,1,0,-1,-1,-1,0,1};int col[]={0,1,1,1,0,-1,-1,-1};//8 direction
//int row[]={2,1,-1,-2,-2,-1,1,2};int col[]={1,2,2,1,-1,-2,-2,-1};//Knight Direction
//int row[]={-1,-1,+0,+1,+1,+0};int col[]={-1,+1,+2,+1,-1,-2}; //Hexagonal Direction

#define ri(N) scanf("%d",&N)
#define rll(N) scanf("%lld",&N)
#define rs(N) scanf("%s",N)
#define eps 1e-9
#define Sort(x) sort(x.begin(),x.end())
#define Reverse(x) reverse(x.begin(),x.end())
#define tonum(c) (c>='A'&&c<='Z'?c-'A' : c-'a'+26)
#define all(X)  X.begin(),X.end()
#define UNIQUE(X)  X.resize(unique(all(X))-X.begin())
#define tr(container,it)  for(typeof(container.begin()) it=container.begin();it!=container.end();it++)
//////////////////////////////////////////////////////////////////////
// Numberic Functions
int day(int y,int m,int d)
{if(m<3){--y;m+=12;}return 365*y+y/4 - y/100+y/400+(153*m - 457)/5+d - 306;}
ll josephus(ll x) // If the 2nd person is killed always then the last man
{return 2*(x-pow(2,(ll)log2(x)))+1;}
ll josephus(ll n,ll x) // If the 2nd person is killed always then the x'th man
{if(n==1&&x==1)return 1;if(n>1&&x==1)return 2;ll res=josephus(n-1,x-1);if(res==n-1)return 1;if(res<=n-2)return res+2;return 0;}
ll survivor(ll n,ll k) // If the k'th person is killed always then the last man
{ll i,s;for(s=0,i=1;i<=n;i++)s=(s+k)%i;return (s+1);}
template<class T> inline T gcd(T a,T b)
{if(a<0)return gcd(-a,b);if(b<0)return gcd(a,-b);return (b==0)?a:gcd(b,a%b);}
template<class T> inline T lcm(T a,T b)
{if(a<0)return lcm(-a,b);if(b<0)return lcm(a,-b);return a*(b/gcd(a,b));}
template<class T> T power(T N,T P)  // a^b
{return (P==0)? 1: N*power(N,P-1);}
template<class T> inline T mod(T N,T M)  // n%mod
{if(N<0)N+=(ceil(-N*1.00/M)*M);return N%M;}
template<class T> T bigmod(T a,T b,T mod)  //(a^b)%mod
{if(b==0)return 1;if(b%2==0){T ret=bigmod(a,b/2,mod);return ((ret%mod)*(ret%mod))%mod;}else return ((a%mod)*(bigmod(a,b-1,mod)%mod))%mod;}
template<class T> inline double distance_point(pair<T,T>P,pair<T,T>Q)
{T X1,X2,Y1,Y2;X1=P.first,Y1=P.second;X2=Q.first,Y2=Q.second;return sqrt((X1-X2)*(X1-X2)+(Y1-Y2)*(Y1-Y2));}
// String conversion
template<class T> string itos(T N){stringstream ss;ss<<N;string Str;Str=ss.str();return Str;}
template<class T> vector<int> vstoi(T Str){stringstream ss(Str);vector<int>A;for(int N;ss>>N;A.push_back(N)){}return A;}
vector<string> split(string str,string Separator)
{vector<string>answer;string temp;for(auto i=0u;i<str.length();i++){bool isSeparator=false;for(auto j=0u;j<Separator.length();j++)if(str[i]==Separator[j])isSeparator=true;if(!isSeparator){temp+=str[i];continue;}if(temp!="")answer.push_back(temp);temp="";}if(temp!="")answer.push_back(temp);return answer;}
// Working with bit
ll check_bit(ll N,int POS){return (N & (1LL<<POS));}
ll on_bit(ll N,int POS){return N | (1LL<<POS);}
ll off_bit(ll N,int POS){return N & ~(1LL<<POS);}
int find_parent(int x)
{if(parent[x]!=x)parent[x]=find_parent(parent[x]);return parent[x];}
string from_decimal_to(ll n, int b)  // Upto base 20
{if(n==0)return "0";string chars="0123456789ABCDEFGHIJ";string result="";while(n>0){result=chars[n%b]+result;n/=b;}return result;}
#define pb push_back
#define ff first
#define ss second
#define MP make_pair
#define ii pair<int,int>
#define pp1 pair<int,pair<int,int> >
#define pp2 pair<pair<int,int>,int >
#define pq(xx) priority_queue<xx,vector<xx>,greater<xx> >
//////////////////////////////////////////////////////////////////////
int batch,ins;
vector<string>batch_name;

vector<string>courses;
map<string,int>course_no;
double credit[50];
vector<int>course_instructor[50];
vector<string>lab_courses,theory_courses;
vector<string>batch_lab_courses[10],batch_theory_courses[10];

vector<string>instructor;
vector<int>no_of_course;
vector<string>instructor_course[50];
vector<vector<int> >time_slot(50,vector<int>(50,0));
vector<ii>lab[50],theory[50];

int comp(pair<int,int>p,pair<int,int>q)
{
    int x=p.ss%3,y=q.ss%3;
    x==0?x=3:x;
    y==0?y=3:y;
    if(x==y)
        return p.ff>q.ff;
    return x>y;
}

class input
{
public:
    int take_courses_info();
    int take_instructors_info();
};
int input::take_courses_info()
{
    stdin = freopen("Batch_info.txt","r",stdin);
    string str;
    vector<string>temp;
    courses.push_back("");
    batch_name.push_back("");

    getline(cin,str);
    temp=split(str," ");
    batch=stoi(temp[2]);
    int cnt=1;
    for(auto i=1;i<=batch;i++) // Taking total courses of each batch
    {
        getline(cin,str);
        getline(cin,str);
        temp=split(str," ");
        batch_name.push_back(temp[2]);
        getline(cin,str);
        temp=split(str," ");
        auto n=stoi(temp[2]);
        getline(cin,str);
        for(auto j=1;j<=n;j++)
        {
            getline(cin,str);
            temp=split(str," -");
            str=temp[0]+" "+temp[1];
            courses.push_back(str);
            credit[cnt]=atof(temp[2].c_str());
            course_no[str]=cnt++;
            if(str[str.size()-1]%2==0) // Determining if lab or theory
            {
                lab_courses.push_back(str);
                batch_lab_courses[i].push_back(str);
            }
            else
            {
                theory_courses.push_back(str);
                batch_theory_courses[i].push_back(str);
            }
        }
    }
    fclose(stdin);
    return 0;
}
int input::take_instructors_info()
{
    stdin = freopen("Instructor_info.txt","r",stdin);
    string str;
    vector<string>temp;
    instructor.push_back("");
    no_of_course.push_back(0);
    getline(cin,str);
    temp=split(str," ");
    ins=stoi(temp[2]);
    getline(cin,str);
    for(auto i=1;i<=ins;i++)
    {
        getline(cin,str);
        temp=split(str," ");
        instructor.push_back(temp[2]);
        getline(cin,str);
        temp=split(str," ");
        no_of_course.push_back(stoi(temp[2]));
        getline(cin,str);
        for(auto j=0;j<no_of_course[i];j++) // Each instructor's courses
        {
            getline(cin,str);
            instructor_course[i].push_back(str);
            course_instructor[course_no[str]].push_back(i);
        }
        int m, cnt=1;
        for(auto j=0;j<5;j++) // Each instructors favoured time slots
        {
            cin>>str>>str;
            for(auto k=1;k<=9;k++)
            {
                cin>>m;
                time_slot[i][cnt++]=m;
            }
            // lab period select for each instructor
            if(time_slot[i][j*9+1]&&time_slot[i][j*9+2]&&time_slot[i][j*9+3])
            {
                int a,b,c;
                a=time_slot[i][j*9+1];
                b=time_slot[i][j*9+2];
                c=time_slot[i][j*9+3];
                lab[i].push_back(MP(a+b+c,j*3+1));
            }
            if(time_slot[i][j*9+4]&&time_slot[i][j*9+5]&&time_slot[i][j*9+6])
            {
                int a,b,c;
                a=time_slot[i][j*9+4];
                b=time_slot[i][j*9+5];
                c=time_slot[i][j*9+6];
                lab[i].push_back(MP(a+b+c,j*3+2));
            }
            if(time_slot[i][j*9+7]&&time_slot[i][j*9+8]&&time_slot[i][j*9+9])
            {
                int a,b,c;
                a=time_slot[i][j*9+7];
                b=time_slot[i][j*9+8];
                c=time_slot[i][j*9+9];
                lab[i].push_back(MP(a+b+c,j*3+3));
            }
        }
        getline(cin,str);
        getline(cin,str);
    }
    fclose(stdin);
    return 0;
}

int maxi_lab=-(1<<20),total_solved_lab=0;
vector<string>name_lab;
map<int,int>batch_lab;
pair<int,int> lab_ins[50];
vector<ii> lab_slot[50];
int lab_side[50],lab_side_temp[50],lab_side_final[50];
int ins_days_lab[50][7],ins_days_lab_temp[50][7],ins_days_lab_final[50][7];
int used_slot_for_lab[50][20],used_slot_for_lab_temp[50][20],used_slot_for_lab_final[50][20];
int batch_days_lab[30][7],batch_days_lab_temp[30][7],batch_days_lab_final[30][7];
int batch_free_slot[10][50];

class manage_lab_slot
{
public:
    int lab_violation(int x,int slot,int cur_batch);
    int copy_best();
    int copy_best_final();
    int make_rand();
    int manage_lab();
};
int manage_lab_slot::copy_best()
{
    for(int i=0;i<30;i++)
    {
        for(int j=0;j<7;j++)
            batch_days_lab[i][j]=batch_days_lab_temp[i][j];
    }
    for(int i=0;i<50;i++)
    {
        lab_side[i]=lab_side_temp[i];
        for(int j=0;j<7;j++)
            ins_days_lab[i][j]=ins_days_lab_temp[i][j];
        for(int j=0;j<20;j++)
            used_slot_for_lab[i][j]=used_slot_for_lab_temp[i][j];
    }
    return 0;
}
int manage_lab_slot::copy_best_final()
{
    for(int i=0;i<30;i++)
    {
        for(int j=0;j<7;j++)
            batch_days_lab_final[i][j]=batch_days_lab[i][j];
    }
    for(int i=0;i<50;i++)
    {
        lab_side_final[i]=lab_side[i];
        for(int j=0;j<7;j++)
            ins_days_lab_final[i][j]=ins_days_lab[i][j];
        for(int j=0;j<20;j++)
            used_slot_for_lab_final[i][j]=used_slot_for_lab[i][j];
    }
    return 0;
}
int manage_lab_slot::lab_violation(int x,int slot,int cur_batch)
{
    int slot_day;
    if(slot%3==0)
        slot_day=slot/3;
    else
        slot_day=slot/3+1;
    // Hard constraint check
    if(cur_batch%3==0)
    {
        if(batch_days_lab_temp[cur_batch-1][slot_day]&&batch_days_lab_temp[cur_batch-2][slot_day])
        {
            string str=name_lab[batch_days_lab_temp[cur_batch-1][slot_day]];
            vector<string>temp=split(str," ()");
            str=temp[0]+" "+temp[1];
            int n=course_no[str];
            if(credit[n]==1.5)
                return -2;
        }
        else if(batch_days_lab_temp[cur_batch-1][slot_day]||batch_days_lab_temp[cur_batch-2][slot_day])
            return -2;
    }
    else
    {
        if(batch_days_lab_temp[cur_batch][slot_day])
            return -2;
    }

    pair<int,int>p=lab_ins[x];
    int ins1=p.ff;
    int ins2=p.ss;

    if(used_slot_for_lab_temp[ins1][slot]||used_slot_for_lab_temp[ins2][slot])
        return -2;
    if(ins_days_lab_temp[ins1][slot_day]==2||ins_days_lab_temp[ins2][slot_day]==2)
        return -2;

    // Soft constraint calculation
    int total=0;
    if(ins_days_lab_temp[ins1][slot_day])
        total++;
    if(ins_days_lab_temp[ins2][slot_day])
        total++;
    if(slot%3)
        total++;
    return total;
}
int manage_lab_slot::make_rand()
{
    int cnt=name_lab.size();
    for(auto i=1;i<cnt;i++)
    {
        int m=lab_slot[i].size();
        for(auto j=0;j<m/2-2;j++)
        {
            int p=rand()%m;
            swap(lab_slot[i][j],lab_slot[i][p]);
        }
    }
    return 0;
}
int manage_lab_slot::manage_lab()
{
    name_lab.push_back("");
    int cnt=1;
    int m=1, n;
    for(auto i=1;i<=batch;i++) // Allocating possible time slot for every lab
    {
        for(auto j=0u;j<batch_lab_courses[i].size();j++)
        {
            n=course_no[batch_lab_courses[i][j]];
            int ins1=course_instructor[n][0];
            int ins2=course_instructor[n][1];
            vector<ii>temp;
            for(auto k=0u;k<lab[ins1].size();k++)
            {
                for(auto l=0u;l<lab[ins2].size();l++)
                {
                    auto p=lab[ins1][k].ss;
                    auto q=lab[ins2][l].ss;
                    if(p==q&&!used_slot_for_lab[ins1][p]&&!used_slot_for_lab[ins2][q])
                    {
                        int sum=lab[ins1][k].ff+lab[ins2][l].ff;
                        temp.push_back(MP(sum,p));
                    }
                }
            }
            if(credit[n]==1.5)
            {
                name_lab.push_back(batch_lab_courses[i][j]+"(A)");
                batch_lab[cnt]=m;
                lab_ins[cnt]=MP(ins1,ins2);
                lab_slot[cnt++]=temp;

                name_lab.push_back(batch_lab_courses[i][j]+"(B)");
                batch_lab[cnt]=m+1;
                lab_ins[cnt]=MP(ins1,ins2);
                lab_slot[cnt++]=temp;
            }
            else
            {
                name_lab.push_back(batch_lab_courses[i][j]+"(A/B)");

                batch_lab[cnt]=m+2;
                lab_ins[cnt]=MP(ins1,ins2);
                lab_slot[cnt++]=temp;
            }
        }
        m=m+3;
    }
    double pheromone[cnt+1][20],evprate=0.7;
    for(auto i=1;i<cnt;i++)
    {
        for(auto j=1;j<=15;j++)
            pheromone[i][j]=1/evprate; // 1/ro where ro=0.7
    }
    int generation=0;
    double max_pheromone=-(1<<20);
    while(++generation<500)
    {
        int ant=0,solved=0,maxi_temp=-(1<<20);
        while(++ant<500)
        {
            memset(lab_side_temp,0,sizeof(lab_side_temp));
            memset(batch_days_lab_temp,0,sizeof(batch_days_lab_temp));
            memset(used_slot_for_lab_temp,0,sizeof(used_slot_for_lab_temp));
            memset(ins_days_lab_temp,0,sizeof(ins_days_lab_temp));
            int total=0,solved_temp=0;
            for(auto i=1;i<cnt;i++)
            {
                pair<int,int>inst=lab_ins[i];
                int ins1=inst.ff;
                int ins2=inst.ss;
                int cur_batch=batch_lab[i];

                vector<pair<double,int> >probability;
                double total_prob=0,z=0;
                for(auto j=0u;j<lab_slot[i].size();j++)
                {
                    int slot=lab_slot[i][j].ss;
                    double hur=pheromone[i][lab_slot[i][j].ss]*(1.00/(1+lab_violation(i,slot,cur_batch)));
                    if(hur>0)
                    {
                        probability.push_back(MP(hur,j));
                        total_prob+=probability[z++].ff;
                    }
                }
                for(auto j=0;j<z;j++)
                    probability[j].ff/=total_prob;
                sort(probability.rbegin(),probability.rend());
                /*
                for(j=0;j<z;j++)
                  printf("%d : %.2lf\n",probability[j].ss,probability[j].ff);
                */
                if(!z)
                    continue;
                m=z*0.7;
                m==0?m++:m;

                int q=rand()%m;
                int p=probability[q].ss;
                int slot=lab_slot[i][p].ss;
                int slot_day;
                if(slot%3==0)
                    slot_day=slot/3;
                else
                    slot_day=slot/3+1;

                if(cur_batch%3==0)
                    batch_days_lab_temp[cur_batch][slot_day]=batch_days_lab_temp[cur_batch-1][slot_day]=batch_days_lab_temp[cur_batch-2][slot_day]=i;
                else
                    batch_days_lab_temp[cur_batch][slot_day]=i;
                lab_side_temp[i]=slot;
                used_slot_for_lab_temp[ins1][slot]=used_slot_for_lab_temp[ins2][slot]=i;
                ins_days_lab_temp[ins1][slot_day]++;
                ins_days_lab_temp[ins2][slot_day]++;

                total+=lab_slot[i][p].ff;
                solved_temp++;
            }
            if((total>maxi_temp&&solved_temp==solved)||solved_temp>solved)
            {
                copy_best();  // Saving best solution
                solved=solved_temp;
                maxi_temp=total;
            }
            make_rand();
        }
        if(solved>=total_solved_lab)
        {
            double val=0;
            for(auto i=1;i<cnt;i++)
            {
                for(auto j=1;j<=15;j++)
                {
                    if(lab_side[i]==j)
                    {
                        pheromone[i][j]=(1-evprate)*pheromone[i][j]+2;// (1-ro)*tau+2
                        val+=pheromone[i][j];
                    }
                    else
                        pheromone[i][j]=(1-evprate)*pheromone[i][j]; // (1-ro)*tau
                }
            }
            // to print pheromone for every generation
            /*for(i=1;i<cnt;i++)
            {
                for(j=1;j<=45;j++)
                {
                    printf("%.2lf ",pheromone[i][j]);
                }
                printf("\n");
            }
            printf("\n");*/
            if((solved==total_solved_lab && val+maxi_temp>max_pheromone)||solved>total_solved_lab)
            {
                cout<<"Prev assigned : "<<total_solved_lab<<" Current assigned : "<<solved<<"\n";
                cout<<"Prev max pheromone : "<<max_pheromone<<" Current pheromone : "<<val+maxi_temp<<"\n\n";
                maxi_lab=maxi_temp;
                total_solved_lab=solved;
                max_pheromone=val+maxi_temp;
                copy_best_final();
            }
        }
    }
    printf("\n*********** End of lab assignment ***********\n\n");
    // making the time slot visited for each instructor and batch in which lab are assigned
    for(auto i=1;i<=ins;i++)
        for(auto j=1;j<=15;j++)
            if(used_slot_for_lab_final[i][j]||j%3==0)
                time_slot[i][j*3-2]=time_slot[i][j*3-1]=time_slot[i][j*3]=0;
    for(auto i=1;i<=batch;i++)
    {
        for(auto j=1;j<cnt;j++)
        {
            if(lab_side_final[j]&&batch_lab[j]>3*(i-1)&&batch_lab[j]<=3*i)
            {
                batch_free_slot[i][lab_side_final[j]*3]=1;
                batch_free_slot[i][lab_side_final[j]*3-1]=1;
                batch_free_slot[i][lab_side_final[j]*3-2]=1;
            }
        }
    }
    return 0;
}

int maxi_class=-(1<<20),total_solved_class=0;
vector<string>name_theory;
map<int,int>batch_theory;
vector<ii>theory_slot[80];
vector<int>theory_ins[80];
vector<int>course_slot[50];
int selective_slot[80],selective_slot_temp[80],selective_slot_final[80];
int batch_slot_class[10][50],batch_slot_class_temp[10][50],batch_slot_class_final[10][50];
int ins_days_class[50][7],ins_days_class_temp[50][7],ins_days_class_final[50][7];
int batch_days_class[10][7],batch_days_class_temp[10][7],batch_days_class_final[10][7];
int used_slot_for_class[50][50],used_slot_for_class_temp[50][50],used_slot_for_class_final[50][50];

class manage_class_slot
{
public:
    int copy_best();  // Saving the local best result
    int copy_best_final();  // Saving the global best result
    int class_violation(int x,int slot,int n);
    int can_put(int x,int slot,int n);  // Checking if the theory class in a time slot violating a hard constraint
    int make_rand();
    int mutate(int cnt);
    int manage_class();
};
int manage_class_slot::copy_best()
{
    for(int i=0;i<10;i++)
    {
        for(int j=0;j<7;j++)
            batch_days_class[i][j]=batch_days_class_temp[i][j];
        for(int j=0;j<50;j++)
            batch_slot_class[i][j]=batch_slot_class_temp[i][j];
    }
    for(int i=0;i<50;i++)
    {
        for(int j=0;j<7;j++)
            ins_days_class[i][j]=ins_days_class_temp[i][j];
        for(int j=0;j<50;j++)
            used_slot_for_class[i][j]=used_slot_for_class_temp[i][j];
    }
    for(int i=0;i<80;i++)
        selective_slot[i]=selective_slot_temp[i];
    return 0;
}
int manage_class_slot::copy_best_final()
{
    for(int i=0;i<10;i++)
    {
        for(int j=0;j<7;j++)
            batch_days_class_final[i][j]=batch_days_class[i][j];
        for(int j=0;j<50;j++)
            batch_slot_class_final[i][j]=batch_slot_class[i][j];
    }
    for(int i=0;i<50;i++)
    {
        for(int j=0;j<7;j++)
            ins_days_class_final[i][j]=ins_days_class[i][j];
        for(int j=0;j<50;j++)
            used_slot_for_class_final[i][j]=used_slot_for_class[i][j];
    }
    for(int i=0;i<80;i++)
        selective_slot_final[i]=selective_slot[i];
    return 0;
}
int manage_class_slot::can_put(int x,int slot,int n)
{
    int slot_day;
    if(slot%9==0)
        slot_day=slot/9;
    else
        slot_day=slot/9+1;
    int cur_batch=batch_theory[x];
    if(batch_slot_class_temp[cur_batch][slot]||batch_days_class_temp[cur_batch][slot_day]>=4)
        return 0;
    for(auto i=0u;i<course_slot[n].size();i++)
        if(course_slot[n][i]==slot_day)
            return 0;
    for(auto i=0u;i<theory_ins[x].size();i++)
    {
        int ins=theory_ins[x][i];
        if(used_slot_for_class_temp[ins][slot]||ins_days_class_temp[ins][slot_day]>=2)
            return 0;
    }
    return 1;
}
int manage_class_slot::class_violation(int x,int slot,int n)
{
    // For hard constraint violation
    int slot_day;
    if(slot%9==0)
        slot_day=slot/9;
    else
        slot_day=slot/9+1;
    int cur_batch=batch_theory[x];
    if(batch_slot_class_temp[cur_batch][slot])
        return -2;
    for(auto i=0u;i<course_slot[n].size();i++)
        if(course_slot[n][i]==slot_day)
            return -2;
    for(auto i=0u;i<theory_ins[x].size();i++)
    {
        int ins=theory_ins[x][i];
        if(used_slot_for_class_temp[ins][slot])
            return -2;
    }

    // Soft constraint calculation
    int total=0;
    if(batch_days_class_temp[cur_batch][slot_day]>=3)
        total++;

    int ins1=theory_ins[x][0],ins2;
    if(theory_ins[x].size()>1)
        ins2=theory_ins[x][1];
    else
        ins2=0;
    if(used_slot_for_class_temp[ins1][slot_day]>=2)
        total++;
    if(used_slot_for_class_temp[ins2][slot_day]>=2)
        total++;
    if(used_slot_for_class_temp[ins1][slot-1])
        total++;
    if(used_slot_for_class_temp[ins1][slot+1])
        total++;
    if(used_slot_for_class_temp[ins2][slot-1])
        total++;
    if(used_slot_for_class_temp[ins2][slot+1])
        total++;
    return total;
}
int manage_class_slot::make_rand()
{
    int cnt=name_theory.size();
    for(auto i=1;i<cnt;i++)
    {
        auto m=theory_slot[i].size();
        for(auto j=0u;j<m/2-1;j++)
        {
            int p=rand()%m;
            swap(theory_slot[i][j],theory_slot[i][p]);
        }
    }
    return 0;
}
int manage_class_slot::mutate(int cnt)
{
    int course_to_mutate=rand()%cnt;
    if(!selective_slot[course_to_mutate]||theory_ins[course_to_mutate].size()>1||!course_to_mutate)
        return 0;
    int ins=theory_ins[course_to_mutate][0];
    int cur_batch=batch_theory[course_to_mutate];
    int prev_point=time_slot[ins][selective_slot[course_to_mutate]];
    int m=theory_slot[course_to_mutate].size();
    string str=name_theory[course_to_mutate];
    vector<string>temp=split(str," ()");
    str=temp[0]+" "+temp[1];
    int n=course_no[str];
    for(int i=0;i<2*m;i++)
    {
        int p=rand()%m;
        int slot=theory_slot[course_to_mutate][p].ss;
        if(can_put(course_to_mutate,slot,n))
        {
            if(theory_slot[course_to_mutate][p].ff>prev_point)
            {
                selective_slot[course_to_mutate]=slot;
                used_slot_for_class[ins][slot]=course_to_mutate;
                batch_slot_class[cur_batch][slot]=course_to_mutate;
                return theory_slot[course_to_mutate][p].ff-prev_point;
            }
        }
    }
    return 0;
}
int manage_class_slot::manage_class()
{
    for(auto i=1;i<=ins;i++)
    {
        for(auto j=1;j<=45;j++)
        {
            if(time_slot[i][j])
                theory[i].push_back(MP(time_slot[i][j],j));
        }
    }
    name_theory.push_back("");
    int cnt=1, m, n;
    for(auto i=0u;i<theory_courses.size();i++)  // Allocating possible time slot for every theory course
    {
        string str=theory_courses[i];
        m=str[str.size()-4]-'0'; // Getting Batch number
        n=course_no[str];
        int ins1=course_instructor[n][0];
        int ins2=course_instructor[n][1];
        if(credit[n]==2)
        {
            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins1);
            theory_slot[cnt++]=theory[ins1];

            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins2);
            theory_slot[cnt++]=theory[ins2];
        }
        else if(credit[n]==3)
        {
            name_theory.push_back(str+"(c)");
            vector<ii>temp;
            for(auto j=0u;j<theory[ins1].size();j++)
            {
                for(auto k=0u;k<theory[ins2].size();k++)
                {
                    if(theory[ins1][j].ss==theory[ins2][k].ss)
                        temp.push_back(MP(theory[ins1][j].ff+theory[ins2][k].ff,theory[ins1][j].ss));
                }
            }
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins1);
            theory_ins[cnt].push_back(ins2);
            theory_slot[cnt++]=temp;

            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins1);
            theory_slot[cnt++]=theory[ins1];

            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins2);
            theory_slot[cnt++]=theory[ins2];
        }
        else
        {
            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins1);
            theory_slot[cnt++]=theory[ins1];

            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins1);
            theory_slot[cnt++]=theory[ins1];

            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins2);
            theory_slot[cnt++]=theory[ins2];

            name_theory.push_back(str);
            batch_theory[cnt]=m;
            theory_ins[cnt].push_back(ins2);
            theory_slot[cnt++]=theory[ins2];
        }
    }
    for(auto i=1;i<cnt;i++)
    {
        m=theory_slot[i].size();
        for(auto j=0;j<m;j++)
        {
            int slot=theory_slot[i][j].ss;
            int cur_batch=batch_theory[i];
            if(batch_free_slot[cur_batch][slot]) // If batch has lab in this poriod
            {
                swap(theory_slot[i][j],theory_slot[i][m-1]);
                theory_slot[i].pop_back();
                m--;
                j--;
            }
        }
    }
    double pheromone[cnt+1][50],evprate=0.7;
    for(auto i=1;i<cnt;i++)
    {
        for(auto j=1;j<=45;j++)
            pheromone[i][j]=1/evprate; // 1/ro where ro=0.7
    }
    int generation=0;
    double max_pheromone=-(1<<20);
    while(++generation<500)
    {
        int ant=0,solved=0,maxi_temp=-(1<<20);
        while(++ant<500)
        {
            for(auto i=1;i<50;i++)
                course_slot[i].clear();
            memset(selective_slot_temp,0,sizeof(selective_slot_temp));
            memset(batch_days_class_temp,0,sizeof(batch_days_class_temp));
            memset(batch_slot_class_temp,0,sizeof(batch_slot_class_temp));
            memset(used_slot_for_class_temp,0,sizeof(used_slot_for_class_temp));
            memset(ins_days_class_temp,0,sizeof(ins_days_class_temp));
            int total=0,solved_temp=0;
            for(auto i=1;i<cnt;i++)  // for each theory course assign a time slot
            {
                string str=name_theory[i];
                vector<string>temp=split(str," ()");
                str=temp[0]+" "+temp[1];
                n=course_no[str];
                int cur_batch=batch_theory[i];

                vector<pair<double,int> >probability;
                double total_prob=0,z=0;
                for(auto j=0u;j<theory_slot[i].size();j++)
                {
                    double hur=pheromone[i][theory_slot[i][j].ss]*(1.00/(1+class_violation(i,theory_slot[i][j].ss,n)));
                    if(hur>0)
                    {
                        probability.push_back(MP(hur,j));
                        total_prob+=probability[z++].ff;
                    }
                }
                for(auto j=0;j<z;j++)
                    probability[j].ff/=total_prob;
                sort(probability.rbegin(),probability.rend());
                /*
                for(j=0;j<z;j++)
                  printf("%d : %.2lf\n",probability[j].ss,probability[j].ff);
                */
                if(!z)
                    continue;
                m=z*0.7;
                m==0?m++:m;

                int q=rand()%m;
                int p=probability[q].ss;
                int slot=theory_slot[i][p].ss;
                int slot_day;
                if(slot%9==0)
                    slot_day=slot/9;
                else
                    slot_day=slot/9+1;
                batch_days_class_temp[cur_batch][slot_day]++;
                batch_slot_class_temp[cur_batch][slot]=i;
                for(auto k=0u;k<theory_ins[i].size();k++)
                {
                    int ins=theory_ins[i][k];
                    used_slot_for_class_temp[ins][slot]=i;
                    ins_days_class_temp[ins][slot_day]++;
                }
                selective_slot_temp[i]=slot;
                course_slot[n].push_back(slot_day);
                total+=theory_slot[i][p].ff;

                solved_temp++;
            }
            if((total>maxi_temp&&solved_temp==solved)||solved_temp>solved)
            {
                copy_best();  // Saving best solution
                solved=solved_temp;
                maxi_temp=total;
            }
            make_rand();
        }
        if(solved>=total_solved_class)
        {
            maxi_temp+=mutate(cnt); // Mutation of one course if result is good
            double val=0;
            for(auto i=1;i<cnt;i++)
            {
                for(auto j=1;j<=45;j++)
                {
                    if(selective_slot[i]==j)
                    {
                        pheromone[i][j]=(1-evprate)*pheromone[i][j]+2;// (1-ro)*tau+2
                        val+=pheromone[i][j];
                    }
                    else
                        pheromone[i][j]=(1-evprate)*pheromone[i][j]; // (1-ro)*tau
                }
            }
            // to print pheromone for every generation
            /*for(i=1;i<cnt;i++)
            {
                for(j=1;j<=45;j++)
                {
                    printf("%.2lf ",pheromone[i][j]);
                }
                printf("\n");
            }
            printf("\n");*/
            if((solved==total_solved_class && val+maxi_temp>max_pheromone)||solved>total_solved_class)
            {
                cout<<"Prev assigned : "<<total_solved_class<<" Current assigned : "<<solved<<"\n";
                cout<<"Prev max pheromone : "<<max_pheromone<<" Current pheromone : "<<val+maxi_temp<<"\n\n";
                maxi_class=maxi_temp;
                total_solved_class=solved;
                max_pheromone=val+maxi_temp;
                copy_best_final();
            }
        }
    }
    printf("\n*********** End of class assignment ***********\n\n");
    // to print final pheromone
    /*for(i=1;i<cnt;i++)
    {
        for(j=1;j<=45;j++)
        {
            printf("%.2lf ",pheromone[i][j]);
        }
        printf("\n");
    }*/
    return 0;
}

class print
{
public:
    int print_input_data();
    int print_lab();
    int print_class();
    int print_routine();
};
int print::print_input_data()
{
    cout<<"Total Courses and Instructors :\n";
    for(auto i=1u;i<courses.size();i++)
    {
        if(courses[i][courses[i].size()-1]%2==0)
            continue;
        auto j=course_no[courses[i]];
        cout<<courses[i]<<" : ";
        for(auto k=0u;k<course_instructor[j].size();k++)
        {
            cout<<instructor[course_instructor[j][k]];
            if(k==0)
                printf(" and ");
        }
        cout<<"\n";
    }
    printf("\n******************* Information of Instructors *******************\n");
    for(auto i=1;i<=ins;i++)
    {
        cout<<"\n/////////////////////////////\n";
        cout<<instructor[i]<<"\n";
        cout<<"\nCourses :\n";
        for(auto j=0u;j<instructor_course[i].size();j++)
        {
            if(instructor_course[i][j][instructor_course[i][j].size()-1]%2)
                cout<<instructor_course[i][j]<<"\n";
        }
        cout<<"\nTime_Slot :\n";
        for(auto j=1;j<=45;j++)
        {
            printf(" %d",time_slot[i][j]);
            if(j%9==0)
                printf("\n");
        }
    }
    cout<<"\n";
    return 0;
}
int print::print_lab()
{
    printf("******************* Lab Allocation *******************\n\n");
    int cnt=name_lab.size();
    printf("******************* Suitable lab_slot *******************\n");
    for(auto i=1;i<cnt;i++)
    {
        printf("%-15s:",name_lab[i].c_str());
        for(auto j=0u;j<lab_slot[i].size();j++)
            cout<<" "<<lab_slot[i][j].ss;
        cout<<"\n";
    }
    cout<<"\n";
    printf("******************* Allocated lab_slot *******************\n");
    for(auto i=1;i<cnt;i++)
        printf("%-15s: %d\n",name_lab[i].c_str(),lab_side_final[i]);
    cout<<"\n";
    printf("%55s%48s%48s%48s%48s\n","SUN","MON","TUE","WED","THU");
    for(auto i=1;i<=15*16+30;i++)
        printf("-");
    printf("\n");
    for(auto i=1;i<=ins;i++)
    {
        printf("%-28s :",instructor[i].c_str());
        for(auto j=1;j<=15;j++)
        {
            if(used_slot_for_lab_final[i][j]==0)
                printf("%15s|","");
            else
                printf("%15s|",name_lab[used_slot_for_lab_final[i][j]].c_str());
        }
        printf("\n");
    }
    for(auto i=1;i<=15*16+30;i++)
        printf("-");
    printf("\n");
    for(auto i=1;i<=batch;i++)
    {
        vector<string>temp[16];
        for(auto j=1;j<cnt;j++)
        {
            if(batch_lab[j]>3*(i-1)&&batch_lab[j]<=3*i)
                temp[lab_side_final[j]].push_back(name_lab[j]);
        }
        int maxi=0;
        for(auto j=1;j<=15;j++)
            maxi=max(maxi,(int)temp[j].size());
        printf("%-28s :",batch_name[i].c_str());
        for(auto k=0;k<maxi;k++)
        {
            if(k>0)
                printf("%30s","");
            for(auto j=1;j<=15;j++)
            {
                if((int)temp[j].size()>k)
                    printf("%15s|",temp[j][k].c_str());
                else
                    printf("%15s|","");
            }
            printf("\n");
        }
        for(auto j=1;j<=15*16+30;j++)
            printf("-");
        printf("\n");
    }
    printf("\n\n");
    return 0;
}
int print::print_class()
{
    printf("******************* Class Allocation *******************\n\n");
    int cnt=name_theory.size();
    printf("******************* Suitable class_slot *******************\n");
    for(auto i=1;i<cnt;i++)
    {
        cout<<name_theory[i]<<" : ";
        for(auto j=0u;j<theory_slot[i].size();j++)
            cout<<theory_slot[i][j].ss<<" ";
        cout<<"\n";
    }
    cout<<"\n";
    printf("******************* Allocated class_slot *******************\n");
    for(auto i=1;i<cnt;i++)
        printf("%-15s : %d\n",name_theory[i].c_str(),selective_slot_final[i]);
    printf("%103s%144s%144s%144s%144s\n","SUN","MON","TUE","WED","THU");
    for(auto i=1;i<=45*16+30;i++)
        printf("-");
    printf("\n");
    for(auto i=1;i<=ins;i++)
    {
        printf("%-28s :",instructor[i].c_str());
        for(auto j=1;j<=45;j++)
        {
            if(used_slot_for_class_final[i][j]==0)
                printf("%15s|","");
            else
                printf("%15s|",name_theory[used_slot_for_class_final[i][j]].c_str());
        }
        printf("\n");
    }
    for(auto i=1;i<=45*16+30;i++)
        printf("-");
    printf("\n");
    for(auto i=1;i<=batch;i++)
    {
        vector<string>temp(50,"");
        for(auto j=1;j<cnt;j++)
        {
            string str=name_theory[j];
            int m=batch_theory[j];
            if(m==i)
                temp[selective_slot_final[j]]=name_theory[j];
        }
        printf("%-28s :",batch_name[i].c_str());
        for(auto j=1;j<=45;j++)
        {
            if(temp[j].size())
                printf("%15s|",temp[j].c_str());
            else
                printf("%15s|","");
        }
        printf("\n");
        for(auto j=1;j<=45*16+30;j++)
            printf("-");
        printf("\n");
    }
    printf("\n\n");
    return 0;
}
int print::print_routine()
{
    int cnt=name_lab.size();
    cout<<"Maximam preference : "<<maxi_lab<<"\n";
    cout<<"\nTotal Lab Course : "<<cnt-1<<"\n"<<"\nTotal Assigned : "<<total_solved_lab<<"\n\n";
    for(int i=1;i<cnt;i++)
    {
        if(!lab_side_final[i])
        {
            printf("There is problem in assigning -> %s <- course \n",name_lab[i].c_str());
            printf("Contact with instructor : ");
            printf("%s and %s\n",instructor[lab_ins[i].ff].c_str(),instructor[lab_ins[i].ss].c_str());
            printf("\n");
        }
    }
    cnt=name_theory.size();
    cout<<"Maximam preference : "<<maxi_class<<"\n";
    cout<<"\nTotal Theory Course : "<<cnt-1<<"\n"<<"\nTotal Assigned : "<<total_solved_class<<"\n\n";
    for(int i=1;i<cnt;i++)
    {
        if(!selective_slot_final[i])
        {
            printf("There is problem in assigning -> %s <- course \n",name_theory[i].c_str());
            printf("Contact with instructor : ");
            if(theory_ins[i].size()==1)
                printf("%s\n",instructor[theory_ins[i][0]].c_str());
            else
                printf("%s and %s\n",instructor[theory_ins[i][0]].c_str(),instructor[theory_ins[i][1]].c_str());
            printf("\n");
        }
    }
    printf("******************* Final Routine *******************\n");
    for(auto j=1;j<=45*16+30;j++)
        printf("-");
    cout<<"\n";
    printf("%103s%144s%144s%144s%144s\n","SUN","MON","TUE","WED","THU");
    printf("%38s%16s%16s%16s%16s%16s%16s%16s%16s","1","2","3","4","5","6","7","8","9");
    printf("%16s%16s%16s%16s%16s%16s%16s%16s%16s","1","2","3","4","5","6","7","8","9");
    printf("%16s%16s%16s%16s%16s%16s%16s%16s%16s","1","2","3","4","5","6","7","8","9");
    printf("%16s%16s%16s%16s%16s%16s%16s%16s%16s","1","2","3","4","5","6","7","8","9");
    printf("%16s%16s%16s%16s%16s%16s%16s%16s%16s\n","1","2","3","4","5","6","7","8","9");
    for(auto i=1;i<=45*16+30;i++)
        printf("-");
    printf("\n");
    for(auto i=1;i<=ins;i++)
    {
        printf("%-28s :",instructor[i].c_str());
        for(auto j=1;j<=15;j++)
        {
            if(used_slot_for_lab_final[i][j]==0)
            {
                for(auto k=(j-1)*3+1;k<=j*3;k++)
                    printf("%15s|",name_theory[used_slot_for_class_final[i][k]].c_str());
            }
            else
                printf("%14s->%15s<-%14s|","",name_lab[used_slot_for_lab_final[i][j]].c_str(),"");
        }
        printf("\n");
    }
    for(auto i=1;i<=45*16+30;i++)
        printf("-");
    printf("\n");
    for(auto i=1;i<=batch;i++)
    {
        vector<string>temp1(50,"");
        for(auto j=1u;j<name_theory.size();j++)
        {
            string str=name_theory[j];
            int m=batch_theory[j];
            if(m==i)
                temp1[selective_slot_final[j]]=name_theory[j];
        }
        vector<string>temp2[16];
        for(auto j=1u;j<name_lab.size();j++)
        {
            if(batch_lab[j]>3*(i-1)&&batch_lab[j]<=3*i)
                temp2[lab_side_final[j]].push_back(name_lab[j]);
        }
        int maxi=0;
        for(auto j=1;j<=15;j++)
            maxi=max(maxi,(int)temp2[j].size());
        printf("%-28s :",batch_name[i].c_str());
        for(auto k=0;k<maxi;k++)
        {
            if(k>0)
                printf("%30s","");
            for(auto j=1;j<=15;j++)
            {
                if(temp2[j].size())
                {
                    if((int)temp2[j].size()>k)
                        printf("%14s->%15s<-%14s|","",temp2[j][k].c_str(),"");
                    else
                        printf("%15s|%15s|%15s|","","","");
                }
                else
                {
                    if(k==1)
                    {
                        printf("%15s|%15s|%15s|","","","");
                        continue;
                    }
                    for(auto l=(j-1)*3+1;l<=j*3;l++)
                        printf("%15s|",temp1[l].c_str());
                }
            }
            printf("\n");
        }
        for(auto j=1;j<=45*16+30;j++)
            printf("-");
        printf("\n");
    }
    return 0;
}
int main()
{
    clock_t tt;
    tt=clock();

    input inp;
    inp.take_courses_info();
    inp.take_instructors_info();

    stdout = freopen("Routine.txt","w",stdout);

    print pnt;
    //pnt.print_input_data();

    manage_lab_slot mlab;
    mlab.manage_lab();
    //pnt.print_lab();

    manage_class_slot mclass;
    mclass.manage_class();
    //pnt.print_class();

    pnt.print_routine();

    tt=clock()-tt;
    printf ("\nIt took %.2lf seconds.\n",(double)tt/CLOCKS_PER_SEC);

    fclose(stdout);
    return 0;
}
