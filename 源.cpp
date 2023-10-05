
//22/07/09 1:10 开启项目
//目标帧率：25
//22/07/22 16:00 设计架构  逻辑分辨率：10x24(主界面)+8x20(预览界面) 目标输出分辨率：37x26
//22/07/24 23:00 完成input,newblocks,move,spin初稿
//22/07/22 9:40 完成基本功能
//22/07/29 10:00 修复一些bug,优化boost功能,完成hold功能
//22/08/01 设计preview功能,修补各函数,目标帧率：30
//22/08/01 计划ghostblock功能
//22/08/13 22:00 完成preview功能,修复一些bug,内存占用<1MB
//22/08/14 1:30 设计option,Instruction功能,分离出game函数
//22/08/15 0:30 完成中文语言设计,应用option功能
//22/08/15 1:30 修复一些bug,完成1.0.0.3版本
//22/08/15 10:30 完成SE设计
//22/08/15 14:00 完成Music读取和播放
//22/08/15 17:00 解决一系列bug
//22/08/15 22:30 mcisendstring 查询状态失败,引入GetLong函数解决
//22/08/16 0:50 完成1.0.0.5版本
//22/08/31 22:00 修正一些问题,使用非调试运行库
//22/09/25 12:00 完成1.1.0.1版本,改用计时器判定下落,提供更改帧率限制选项，重新设计设置界面,目标帧率：30/60/144/Unlimited
//22/10/01 0:30 完成1.2.0.1版本,改用高精度时间(ns),修复一些bug,优化帧率显示，优化输出流
//22/10/01 1:30 修复一些bug,提供更改速度限制选项,内存占用<16MB
//22/10/16 23:00 完成1.3.0.1版本,添加存档系统
//22/10/18 0:20 优化输出逻辑，增加暂时加速功能
//22/10/23 8:20 修复一些bug,调整交互界面
//22/10/25 0:35 修复一些bug,调整交互界面
//22/11/04 00:10 添加kickwall功能，停止维护
#include <cstdio>
#include <string>

#include <iostream>

#include <conio.h>
#include<chrono>
#include <windows.h>
//#include <filesystem>
#include <fstream>
#include <string.h>
#include <io.h>
#include <process.h>
#include<Mmsystem.h>
#pragma comment(lib,"winmm.lib")
#include <openssl/md5.h>
#pragma comment(lib, "libcrypto_static.lib")
typedef std::chrono::high_resolution_clock Clock;
using namespace std;
CONSOLE_FONT_INFOEX cfi;
CONSOLE_CURSOR_INFO CursorInfo;
const int lines = 24, cols = 10, maxlength = 40, randmin = 3;
const float minspeed = 0.7, maxspeed1=0.1 ,maxspeed2 = 0.2, maxspeed3=0.3;
int x[maxlength + 4] = { 0 }, y[maxlength + 4] = { 0 }, d[lines + 1][cols + 1], frame, randmaxl = lines - 2 * randmin - 4, randmaxc = cols - 2 * randmin + 2,  score, blocknum, posxtemp, dur20;
int fontsize, language = 1, musicnum = 0, musiclength[33] = {0}, cframelimit = 3, cspeedlimit = 2;
int nScreenWidth = GetSystemMetrics(SM_CXSCREEN), nScreenHeight = GetSystemMetrics(SM_CYSCREEN);
bool status_pause = 0, status_hold = 0, option_preview = 1, option_SE = 1, option_music = 0, option_hold = 1, fontsizechanged = 0, SE_allow = 1,logged=0;
const string s1 = "  ", s2 = "■", s3 = "●", s4 = "▲", s5 = "**", s6 = "\n", s7 = "|", s8 = "--";
const int frametime1 = 33330000, frametime2=16670000, frametime3=6940000;//单位:纳秒
string strbuff, status, cutline, waitline, previewbuff[lines + 1], spacebuff, musicsource[33],username="", md5buf;
Clock::time_point start, end, startb, endb,tstart,tend;
int dur, cframetime= frametime3, ntime, status_boost = 0,kickwalltemp=0,scorecolor=2;
float fps, dropspeed,maxspeed= maxspeed2;
//float fps1 = 0;
HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
COORD coordScreen = { 0, 0 };    // home for the cursor
SYSTEMTIME currenttime;
volatile bool g_bEndMusicThread;
volatile int musicmessage = 0;
struct blockgroup	//基本方块组参数
{
	int type = 0;
	int direction = 0;
	int posx[4] = { 0 };
	int posy[4] = { 0 };

};
blockgroup cb[5];
struct stringgroup
{
	string filename;
	string content;
	LPCWSTR Lfilename = NULL;
};
stringgroup apc[8];
//string result23;
struct recordgroup
{
	string name = "";
	int score = 0;
	int time = 0;
	//int totaltime = 0;
};
recordgroup record[8], personalrecord[16];
bool md5_verify(int filenum)
{


	MD5_CTX ctx;
	int len = 0;
	unsigned char buffer[1024] = { 0 };
	unsigned char digest[16] = { 0 };
	const char* k = apc[filenum].filename.c_str();
	FILE* pFile;
	errno_t err;

	if (err = fopen_s(&pFile, k, "rb") != 0)
	{

		return 0;
	}

	MD5_Init(&ctx);
	if (pFile == 0)
	{

		
		return 0;
	}
	while ((len = fread(buffer, 1, 1020, pFile)) > 0)
	{
		MD5_Update(&ctx, buffer, len);
	}

	MD5_Final(digest, &ctx);

	fclose(pFile);


	int i = 0;
	char buf[33] = { 0 };
	char tmp[3] = { 0 };
	for (i = 0; i < 16; i++)
	{
		sprintf_s(tmp, "%02X", digest[i]);
		strcat_s(buf, tmp);
	}

	char cp[33];
	for (int i = 0; i < 32; i++)
	{
		cp[i] = apc[filenum].content[i];
	}
	cp[32] = '\0';


	if (strcmp(cp, buf) == 0)
	{

		return 1;
	}
	else
	{

		return 0;
	}

}
int md5_verify(const char* k,string md5)
{


	MD5_CTX ctx;
	int len = 0,check=0;
	unsigned char buffer[1024] = { 0 };
	unsigned char digest[16] = { 0 };
	
	FILE* pFile;
	errno_t err;

	if (err = fopen_s(&pFile, k, "rb") != 0)
	{

		return -1;
	}

	MD5_Init(&ctx);
	if (pFile == 0)
	{


		return -1;
	}
	while ((len = fread(buffer, 1, 1020, pFile)) > 0)
	{
		MD5_Update(&ctx, buffer, len);
	}

	MD5_Final(digest, &ctx);

	fclose(pFile);


	int i = 0;
	char buf[33] = { 0 };
	char tmp[3] = { 0 };
	for (i = 0; i < 16; i++)
	{
		sprintf_s(tmp, "%02X", digest[i]);
		strcat_s(buf, tmp);
	}



	md5buf = buf;

	check = (int)buf[1] * (int)buf[10] + (int)buf[2] * (int)buf[9];



		return check;
	

}
LPCWSTR stringToLPCWSTR(string orig)
{
	size_t origsize = orig.length() + 1;
	const size_t newsize = 100;
	size_t convertedChars = 0;
	wchar_t* wcstring = (wchar_t*)malloc(sizeof(wchar_t) * (orig.length() - 1));
	mbstowcs_s(&convertedChars, wcstring, origsize, orig.c_str(), _TRUNCATE);

	return wcstring;
}
/*
char* LPWSTRToLPSTR(LPWSTR lpwszStrIn)
{
	LPSTR pszOut = NULL;
	try
	{
		if (lpwszStrIn != NULL)
		{
			int nInputStrLen = wcslen(lpwszStrIn);

			// Double NULL Termination
			int nOutputStrLen = WideCharToMultiByte(CP_ACP, 0, lpwszStrIn, nInputStrLen, NULL, 0, 0, 0) + 2;
			pszOut = new char[nOutputStrLen];

			if (pszOut)
			{
				memset(pszOut, 0x00, nOutputStrLen);
				WideCharToMultiByte(CP_ACP, 0, lpwszStrIn, nInputStrLen, pszOut, nOutputStrLen, 0, 0);
			}
		}
	}
	catch (std::exception e)
	{
	}

	return pszOut;
}
*/


int ReadFile(const char* filename, string filebuf[64])
{
	ifstream file;
	int num = 0;
	file.open(filename);
	if (file.is_open())
	{
		while (getline(file, filebuf[num]))
		{
			if (filebuf[num] == "")
			{
				continue;
			}
			else
			{
				num++;
				if (num == 64)
				{
					MessageBox(NULL, "读取文件超过filebuf[64]范围", "IO Warning", MB_OK | MB_ICONWARNING);
					break;
				}
			}
		}
		file.close();
		return num;
	}
	else
	{
		return -1;
	}
}
bool WriteFile(const char* filename, string filebuf[64])
{
	ofstream file;
	file.open(filename, ios::out);
	if (file.is_open())
	{
		for (int i = 0; i < 64; i++)
		{
			if (filebuf[i] == "")
			{
				break;
			}
			file << filebuf[i] << endl;
		}
		file.close();
		return 1;
	}
	else
	{
		string err="WriteFile Error!\n";
		err += filename;
		MessageBox(NULL, err.c_str(), "IO Error", MB_OK | MB_ICONSTOP);
		return 0;
	}
}
void certfile(const char* k1, const char* k2)
{
	int check = 0;
	string writebuff[64] = { "" };
	check = md5_verify(k1, md5buf);
	if (check != -1)
	{
		writebuff[0] = md5buf;
		writebuff[1] = to_string(check);
		WriteFile(k2, writebuff);
	}
	
	//cout << md5buf << " a ";
	//char c = _getch();
	return;
}
void fileinit()
{
	string readbuf[64] = { "" }, writebuf[64] = { "" }, writebuf2[64] = { "" };
	writebuf[0] = "[Name]";
	writebuf[1] = "[Score]";
	writebuf[2] = "[Time]";
	
	int lines = ReadFile("./save/normalrecord.dat", readbuf),check=0;
	if (lines == -1)
	{
		writebuf[3] = "[Normal]";
		WriteFile("./save/normalrecord.dat", writebuf);
		certfile("./save/normalrecord.dat", "./save/normalrecord.check");
		

	}
	
	lines = ReadFile("./save/easyrecord.dat", readbuf);
	if (lines == -1)
	{
		writebuf[3] = "[Easy]";
		WriteFile("./save/easyrecord.dat", writebuf);
		certfile("./save/easyrecord.dat", "./save/easyrecord.check");
	}

	lines = ReadFile("./save/hardrecord.dat", readbuf);
	if (lines == -1)
	{
		writebuf[3] = "[Hard]";
		WriteFile("./save/hardrecord.dat", writebuf);
		certfile("./save/hardrecord.dat", "./save/hardrecord.check");
	}
	return;
}

bool filecheck(const char* k1, const char* k2)
{
	fileinit();
	int check = 0;
	string readbuff[64] = { "" };
	check = md5_verify(k1, md5buf);
	ReadFile(k2, readbuff);
	if (md5buf == readbuff[0] && to_string(check) == readbuff[1])
	{
		return 1;
	}
	else
	{
		return 0;
	}
}

bool save()
{
	const string cn1 = "正在存储...", en1 = "Saving...";
	int curnum = -1, lines = 0, nameline = 0, scoreline=0,timeline = 0, totletimeline = 0,k=0, recnum=0;
	string readbuf[64] = {""}, writebuf[64] = { ""};
	bool saved = 0;
	recordgroup newrec[8];
	ntime= chrono::duration_cast<std::chrono::milliseconds>(tend - tstart).count();
	char c=0;
	//cout << ntime;
	if (language == 1)
	{
		printf("%s", cn1.c_str());
	}
	else if (language == 2)
	{
		printf("%s", en1.c_str());
	}
	fileinit();
	
	if (cspeedlimit == 1)	//hard
	{
		if (!filecheck("./save/hardrecord.dat", "./save/hardrecord.check"))
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		lines=ReadFile("./save/hardrecord.dat", readbuf);
		if (lines == -1)
		{
			MessageBox(NULL, "ReadFile Error!\n./save/hardrecord.dat", "IO Error", MB_OK | MB_ICONSTOP);
			return 0;
		}
		if (readbuf[lines - 1] != "[Hard]")
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat\nchanged", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
	}
	else if (cspeedlimit == 2)	//normal
	{
		if (!filecheck("./save/normalrecord.dat", "./save/normalrecord.check"))
		{
			MessageBox(NULL, "Verify Failed!\n./save/normalrecord.dat", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		lines = ReadFile("./save/normalrecord.dat", readbuf);
		if (lines == -1)
		{
			MessageBox(NULL, "ReadFile Error!\n./save/normalrecord.dat", "IO Error", MB_OK | MB_ICONSTOP);
			return 0;
		}
		if (readbuf[lines - 1] != "[Normal]")
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat\nchanged", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
	}
	else if (cspeedlimit == 3)	//easy
	{
		if (!filecheck("./save/easyrecord.dat", "./save/easyrecord.check"))
		{
			MessageBox(NULL, "Verify Failed!\n./save/easyrecord.dat", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		lines = ReadFile("./save/easyrecord.dat", readbuf);
		if (lines == -1)
		{
			MessageBox(NULL, "ReadFile Error!\n./save/easyrecord.dat", "IO Error", MB_OK | MB_ICONSTOP);
			return 0;
		}
		if (readbuf[lines - 1] != "[Easy]")
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat\nchanged", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		
	}
	for (int i = 0; i < lines; i++)
	{
		if (readbuf[i] == "[Name]")
		{
			nameline = i + 1;
		}
		else if (readbuf[i] == "[Score]")
		{
			scoreline = i + 1;
		}
		else if (readbuf[i] == "[Time]")
		{
			timeline = i + 1;
		}

	}
	if (lines==0||nameline == 0 || scoreline == 0 || timeline == 0)
	{
		MessageBox(NULL, "Format Error!", "File Damaged", MB_OK | MB_ICONSTOP);
		return 0;
	}
	for (int i = nameline; i <= scoreline - 2; i++)
	{
		
		record[k].name = readbuf[i];
		k++;
		if (k >= 8)
		{
			break;
		}
	}
	int recnum2 = k;
	recnum = k;
	k = 0;
	if (recnum == 0)
	{
		writebuf[0] = "[Name]";
		writebuf[1] = username;
		writebuf[2] = "[Score]";
		writebuf[3] = to_string(score);
		writebuf[4] = "[Time]";
		writebuf[5] = to_string(ntime);
		k = 6;
	}
	else
	{
		//cout << recnum<<record[2].name;
		//c = _getch();
		for (int i = scoreline; i < scoreline + recnum; i++)
		{

			record[k].score = atoi(readbuf[i].c_str());
			k++;

		}
		//cout <<  record[2].score;
		//c = _getch();
		k = 0;
		for (int i = timeline; i < timeline + recnum; i++)
		{

			record[k].time = atoi(readbuf[i].c_str());
			k++;
		}
		//cout << record[2].time;
		//c = _getch();
		k = 0;
		//system("cls");
		
		for (int i = 0; i < recnum2; i++)	//转化新排名
		{
			//cout << k<<i;
			if (k >= 8)
			{
				break;

			}
			if (record[i].score < score && !saved)
			{
				//cout << "<";
				saved = 1;
				newrec[k].name = username;
				newrec[k].score = score;
				newrec[k].time = ntime;
				k++;

			}
			else if (record[i].score == score && !saved)
			{
				if (record[i].time > ntime)
				{
					saved = 1;
					newrec[k].name = username;
					newrec[k].score = score;
					newrec[k].time = ntime;
					k++;
				}
			}
			if (k >= 8)
			{
				break;

			}
			if (record[i].name == username)
			{
				recnum--;
				if (saved)
				{
					//cout << "101";
					continue;
				}
				else
				{
					
					return 1;
				}
			}
			//cout << ">";
			newrec[k].name = record[i].name;
			newrec[k].score = record[i].score;
			newrec[k].time = record[i].time;
			k++;
		}
		if (k < 8 && !saved)
		{
			saved = 1;
			newrec[k].name = username;
			newrec[k].score = score;
			newrec[k].time = ntime;
			k++;
		}
		
		
		recnum++;
		if (recnum > 8)
		{
			recnum = 8;
		}
		//cout << recnum <<k<< "\n";
		/*
		for (int i = 0; i < k; i++)
		{
			
			cout << newrec[i].name << newrec[i].score << newrec[i].time << "\n";
		}
		*/
		
		//c = _getch();
		writebuf[0] = "[Name]";
		k = 0;
		for (int i = 1; i <= recnum; i++)
		{
			writebuf[i] = newrec[k].name;
			k++;
		}
		k = 0;
		writebuf[recnum + 1] = "[Score]";
		for (int i = recnum + 2; i <= 2 * recnum + 1; i++)
		{
			writebuf[i] = to_string(newrec[k].score);
			k++;
		}
		k = 0;
		writebuf[2 * recnum + 2] = "[Time]";
		for (int i = 2 * recnum + 3; i <= 3 * recnum + 2; i++)	//完成buff写入
		{
			writebuf[i] = to_string(newrec[k].time);
			k++;
		}
		k = 3 * recnum + 3;
	}
	
	
	if (cspeedlimit == 1)	//hard
	{
		writebuf[k] = "[Hard]";
		if (!WriteFile("./save/hardrecord.dat", writebuf))
		{
			
			return 0;
		}
		certfile("./save/hardrecord.dat", "./save/hardrecord.check");

	}
	else if (cspeedlimit == 2)	//normal
	{
		writebuf[k] = "[Normal]";
		if (!WriteFile("./save/normalrecord.dat", writebuf))
		{
			
			return 0;
		}
		certfile("./save/normalrecord.dat", "./save/normalrecord.check");
	}
	else if (cspeedlimit == 3)	//easy
	{
		writebuf[k] = "[Easy]";
		if (!WriteFile("./save/easyrecord.dat", writebuf))
		{
			
			return 0;
		}
		certfile("./save/easyrecord.dat", "./save/easyrecord.check");
	}
	return 1;
		
}
bool readreord(int level)
{
	int curnum = -1, lines = 0, nameline = 0, scoreline = 0, timeline = 0, totletimeline = 0, k = 0, recnum = 0;
	string readbuf[64] = { "" };
	fileinit();
	if (level == 1)	//hard
	{
		if (!filecheck("./save/hardrecord.dat", "./save/hardrecord.check"))
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		lines = ReadFile("./save/hardrecord.dat", readbuf);
		if (lines == -1)
		{
			MessageBox(NULL, "ReadFile Error!\n./save/hardrecord.dat", "IO Error", MB_OK | MB_ICONSTOP);
			return 0;
		}
		if (readbuf[lines - 1] != "[Hard]")
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat\nchanged", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
	}
	else if (level == 2)	//normal
	{
		if (!filecheck("./save/normalrecord.dat", "./save/normalrecord.check"))
		{
			MessageBox(NULL, "Verify Failed!\n./save/normalrecord.dat", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		lines = ReadFile("./save/normalrecord.dat", readbuf);
		if (lines == -1)
		{
			MessageBox(NULL, "ReadFile Error!\n./save/normalrecord.dat", "IO Error", MB_OK | MB_ICONSTOP);
			return 0;
		}
		if (readbuf[lines - 1] != "[Normal]")
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat\nchanged", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}

	}
	else if (level == 3)	//easy
	{
		if (!filecheck("./save/easyrecord.dat", "./save/easyrecord.check"))
		{
			MessageBox(NULL, "Verify Failed!\n./save/easyrecord.dat", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
		lines = ReadFile("./save/easyrecord.dat", readbuf);
		if (lines == -1)
		{
			MessageBox(NULL, "ReadFile Error!\n./save/easyrecord.dat", "IO Error", MB_OK | MB_ICONSTOP);
			return 0;
		}
		if (readbuf[lines - 1] != "[Easy]")
		{
			MessageBox(NULL, "Verify Failed!\n./save/hardrecord.dat\nchanged", "Access Denied", MB_OK | MB_ICONSTOP);
			return 0;
		}
	}
	for (int i = 0; i < lines; i++)
	{
		if (readbuf[i] == "[Name]")
		{
			nameline = i + 1;
		}
		else if (readbuf[i] == "[Score]")
		{
			scoreline = i + 1;
		}
		else if (readbuf[i] == "[Time]")
		{
			timeline = i + 1;
		}

	}
	if (lines == 0 || nameline == 0 || scoreline == 0 || timeline == 0)
	{
		MessageBox(NULL, "Format Error!", "File Damaged", MB_OK | MB_ICONSTOP);
		return 0;
	}
	for (int i = nameline; i <= scoreline - 2; i++)
	{

		record[k].name = readbuf[i];
		k++;
		if (k >= 8)
		{
			break;
		}
	}
	recnum = k;
	k = 0;
	if (recnum == 0)
	{
		if (language == 1)
		{
			cout << "     无记录\n\n";
		}
		else if (language == 2)
		{
			cout << "     No Record\n\n";
		}
		
	}
	else
	{
		for (int i = scoreline; i < scoreline + recnum; i++)
		{

			record[k].score = atoi(readbuf[i].c_str());
			k++;

		}

		k = 0;
		for (int i = timeline; i < timeline + recnum; i++)
		{

			record[k].time = atoi(readbuf[i].c_str());
			k++;
		}
		k = 0;
		for (int i = 0; i < recnum; i++)
		{
			cout << " " << i + 1 << "# " << record[i].name;
			for (int j = 9; j >= record[i].name.length(); j--)
			{
				cout << " ";
			}
			if (i == 0)
			{
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 252);
			}
			else
			{
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
			}
			
			cout << record[i].score ; 
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout <<  "    " << record[i].time / 1000<<"." <<(record[i].time % 1000) / 100 << "s\n\n";
		}
	}
	return 1;
}
bool SendToMCI(string command)
{

	if (!mciSendString(command.c_str(), NULL, 0, 0))
		return true;
	return false;
}
/*
string WCharToMByte(LPCWSTR lpcwszStr)
{
	string str;
	DWORD dwMinSize = 0;
	LPSTR lpszStr = NULL;
	dwMinSize = WideCharToMultiByte(CP_OEMCP, NULL, lpcwszStr, -1, NULL, 0, NULL, FALSE);
	if (0 == dwMinSize)
	{
		return "";
	}
	lpszStr = new char[dwMinSize];
	WideCharToMultiByte(CP_OEMCP, NULL, lpcwszStr, -1, lpszStr, dwMinSize, NULL, FALSE);
	str = lpszStr;
	delete[] lpszStr;
	return str;
}

string GetFromMCI(string command)
{
	//string message;
	LPWSTR message = NULL;
	mciSendString(stringToLPCWSTR(command), message, 20, 0);
	string str = WCharToMByte(message);
	return str;
}
unsigned __stdcall ThreadPlayMusic(LPVOID lpParameter)
{
	srand((unsigned)time(NULL) % 10000);
	int pointer = rand() % musicnum + 1;

	//string filepath = musicsource[];

	string Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
	Open = "OPEN ./bgm/Arcaea_Lowiro_pragmatism-resurrection-_Laur.mp3 ALIAS MUSIC";
	string Close = "CLOSE MUSIC";
	string Status = "status MUSIC mode";
	string Play = "PLAY MUSIC";
	string Stop = "STOP MUSIC";

	SendToMCI(Open);	//打开音乐文件
	SendToMCI(Play);
	while (true)
	{
		Sleep(100);
		if (option_music == 0)
		{
			SendToMCI(Stop);
			while (option_music == 0)
			{
				Sleep(100);

			}
			SendToMCI(Play);

		}

		//if ( mciSendString(L"status MUSIC mode", szbuffer, 64, 0))
		//{
		//	strs = LPWSTRToLPSTR(szbuffer);
		//}
		//result23 = GetFromMCI(Status);	//获取音乐状态
		if (!IsPlaying())	//如果音乐停止，播放下一首
		{
			pointer++;
			if (pointer > musicnum)
			{
				pointer = 1;
			}
			SendToMCI(Close);
			Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
			SendToMCI(Open);
			SendToMCI(Play);
		}

		if (g_bEndMusicThread == true)		//接收主线程发送的退出信号
			break;
		if (musicmessage == 1)
		{
			musicmessage = 0;
			pointer--;
			if (pointer <= 0)
			{
				pointer = musicnum;
			}
			SendToMCI(Close);
			Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
			SendToMCI(Open);
			SendToMCI(Play);
		}
		else if (musicmessage == 2)
		{
			musicmessage = 0;
			pointer++;
			if (pointer > musicnum)
			{
				pointer = 1;
			}
			SendToMCI(Close);
			Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
			SendToMCI(Open);
			SendToMCI(Play);
		}
	}
	SendToMCI(Close);	//关闭音乐文件
	return 0;
}
string RefStr="";
bool IsPlaying()
{
	// char RefStr[10];


	mciSendString("status MUSIC mode", &RefStr[0], 16, 0);

		if (RefStr=="stopped" || RefStr=="STOPPED")
			return 0;

	return 1;


}
*/



int GetLong(const char* ad)	//mcisendstring status MUSIC mode 得不到数据,被迫使用此函数,此函数下注释多为debug用途
{

	//MessageBox(NULL, "1", "Warning", MB_OK | MB_ICONWARNING);
	unsigned int len;
	int dev;
	char buffk[128];
	//const char* ad = "d:/11.mp3";
	MCI_OPEN_PARMS open;
	MCI_STATUS_PARMS status;
	MCIERROR err;
	//MessageBox(NULL, "2", "Warning", MB_OK | MB_ICONWARNING);
	open.lpstrElementName = (LPCSTR)ad;//取得文件名
	//MessageBox(NULL, "3", "Warning", MB_OK | MB_ICONWARNING);
	err = mciSendCommand(0, MCI_OPEN, MCI_OPEN_ELEMENT, (DWORD_PTR)&open);//打开文件
	//MessageBox(NULL, "4", "Warning", MB_OK | MB_ICONWARNING);
	if (err) //出错处理
	{

		//MessageBox(NULL, "5", "Warning", MB_OK | MB_ICONWARNING);
		mciGetErrorString(err, buffk, 128);
		string errbuff = ad ;
		errbuff += s1;
		errbuff += buffk;
		MessageBox(NULL, errbuff.c_str(), "Warning", MB_OK | MB_ICONWARNING);
		//cout << buffk << endl;
		return 60 * 5;
	}
	dev = open.wDeviceID;
	status.dwItem = MCI_STATUS_LENGTH;
	mciSendCommand(dev, MCI_STATUS, MCI_WAIT | MCI_STATUS_ITEM, (DWORD_PTR)&status);//关键,取得长度
	len = status.dwReturn; //获取的是毫秒
	mciSendCommand(dev, MCI_CLOSE, 0, NULL);//关闭文件
	len /= 1000;
	//const char* ba = (const char*)len;
	//MessageBox(NULL, ba, "Warning", MB_OK | MB_ICONWARNING);
	return len;
}
//LPWSTR szbuffer = NULL;
unsigned __stdcall ThreadPlayMusic(LPVOID lpParameter)
{
	srand((unsigned)time(NULL) % 10000);
	int pointer = rand() % musicnum + 1;
	time_t musicstart, current;
	//string filepath = musicsource[];
	int dur30=0,countdown;
	string Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
	//Open = "OPEN ./bgm/Arcaea_Lowiro_pragmatism-resurrection-_Laur.mp3 ALIAS MUSIC";
	string Close = "CLOSE MUSIC";
	string Status = "status MUSIC mode";
	string Play = "PLAY MUSIC";
	string Stop = "STOP MUSIC";
	countdown = musiclength[pointer] + 3;
	SendToMCI(Open);	//打开音乐文件

	SendToMCI(Play);
	musicstart = clock();
	while (true)
	{
		Sleep(100);
		
		if (option_music == 0)
		{
			countdown -= dur30;
			SendToMCI(Stop);
			while (option_music == 0)
			{
				Sleep(100);

			}
			SendToMCI(Play);
			musicstart = clock();
		}
		current = clock();
		dur30 = (int)(current - musicstart) / CLOCKS_PER_SEC;
		//if ( mciSendString(L"status MUSIC mode", szbuffer, 64, 0))
		//{
		//	strs = LPWSTRToLPSTR(szbuffer);
		//}
		//result23 = GetFromMCI(Status);	//获取音乐状态
		//MymciSendString();
		if (dur30>countdown)	//如果音乐停止，播放下一首
		{
			pointer++;
			if (pointer > musicnum)
			{
				pointer = 1;
			}
			SendToMCI(Close);
			countdown = musiclength[pointer] + 3;
			Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
			SendToMCI(Open);
			SendToMCI(Play);
			musicstart = clock();
		}
		
		if (g_bEndMusicThread == true)		//接收主线程发送的退出信号
			break;
		if (musicmessage == 1)
		{
			musicmessage = 0;
			pointer--;
			if (pointer <= 0)
			{
				pointer = musicnum;
			}
			SendToMCI(Close);
			countdown = musiclength[pointer] + 3;
			Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
			SendToMCI(Open);
			SendToMCI(Play);
			musicstart = clock();
		}
		else if (musicmessage == 2)
		{
			musicmessage = 0;
			pointer++;
			if (pointer > musicnum)
			{
				pointer = 1;
			}
			SendToMCI(Close);
			countdown = musiclength[pointer] + 3;
			Open = "OPEN ./bgm/" + musicsource[pointer] + " ALIAS MUSIC";
			SendToMCI(Open);
			SendToMCI(Play);
			musicstart = clock();
		}
	}
	SendToMCI(Close);	//关闭音乐文件
	return 0;
}



void md5check()
{
	apc[1].content = "CAC103B0972ADFA7F2FE551D0E039B0F", apc[1].filename = "./sounds/Deemo_Rayark_Menu_Click01.wav";
	apc[2].content = "B83C6E77D1C18DD2A98B1B09CBF1FCE3", apc[2].filename = "./sounds/LoR_ProjectMoon_ch1_FingerSnap.wav";
	apc[3].content = "70157C2A0DEF14A122B7DC54EA39E95B", apc[3].filename = "./sounds/Phigros_PigeonGames_HitSong2.wav";
	apc[4].content = "AE8D9AF3B2C177376E4BC024A367D94A", apc[4].filename = "./sounds/Phigros_PigeonGames_Tap5.wav";
	apc[5].content = "7E907771361C43012ADD44DB0CBE6BC6", apc[5].filename = "./sounds/Phigros_PigeonGames_Tap7.wav";
	apc[6].content = "C929E8C2E2F4AB4715343A01D10040B1", apc[6].filename = "./sounds/Phigros_PigeonGames_Tap6.wav";


	for (int i = 1; i <= 6; i++)
	{
		apc[i].Lfilename = stringToLPCWSTR(apc[i].filename);
	}
	for (int i = 1; i <= 6; i++)
	{
		if (md5_verify(i) == 0)	//校验SE文件
		{
			option_SE = 0;
			SE_allow = 0;

			return;
		}

	}
	return;
}
/*
inline bool endsWith(const string& str, const string& suffix)
{

	if (str.size() < suffix.size()) {
		return false;
	}

	string tstr = str.substr(str.size() - suffix.size());

	return tstr.compare(suffix) == 0;
}
*/


void getFiles(string path /*vector<string>& files,*/)
{
	//文件句柄，win10用long long，win7用long就可以了
	long long hFile = 0;
	//文件信息 

	struct _finddata_t fileinfo;
	string p;
	if ((hFile = _findfirst(p.assign(path).append("/*.mp3").c_str(), &fileinfo)) != -1)
	{
		do
		{
			//如果是目录,迭代之 //如果不是,加入列表 
			/*
			if ((fileinfo.attrib & _A_SUBDIR))
			{
				if (strcmp(fileinfo.name, ".") != 0 && strcmp(fileinfo.name, "..") != 0)
				{
					getFiles(p.assign(path).append("\\").append(fileinfo.name), files, names);
				}
			}
			*/

			if (!(fileinfo.attrib & _A_SUBDIR))
			{
				musicnum++;
				if (musicnum == 33)
				{
					break;
				}
				musicsource[musicnum] = fileinfo.name;
				//files.push_back(p.assign(path).append("\\").append(fileinfo.name));
				//if (endsWith(fileinfo.name, ".mp3"))
				//{
				string buffp = "./bgm/" + musicsource[musicnum];
				//buffp = "C:/Users/zxc/source/repos/Project5/x64/Debug/bgm/Arcaea_Lowiro_pragmatism-resurrection-_Laur.mp3";
				musiclength[musicnum] = GetLong(buffp.c_str());

				//}
				//names.push_back(fileinfo.name);
			}
		} while (_findnext(hFile, &fileinfo) == 0);
		_findclose(hFile);

	}
	return;
}


bool newblocks(int k, int n)
{



	if (k == 1)	//生成
	{
		
		//k = 0;
		//m = rand() % randmaxl + randmin;
		
		for (int i = 0; i <= 2; i++)
		{
			cb[i].type = cb[i + 1].type;
			cb[i].direction = cb[i + 1].direction;
			cb[i].posx[0] = cb[i + 1].posx[0];

		}
		if (cb[2].posx[0] == 5)
		{
			cb[3].posx[0] = 4;
		}
		else
		{
			cb[3].posx[0] = 5;
		}
		//cb[3].posx[0] = rand() % randmaxc + 2*randmin;
		cb[3].direction = rand() % 4 + 1;
		cb[3].type = rand() % 7 + 1;
		cb[0].posx[0] = rand() % randmaxc + randmin;
		cb[0].posy[0] = 3;
	
	}
	else if (k == 2)
	{
		for (int i = 1; i <= 3; i++)	//更新preview方块组
		{
			newblocks(0, i);
		}
		bool x = 0;
		for (int i = 5; i <= 18; i++)
		{
			previewbuff[i] = "";
		}
		for (int i = 5; i <= 8; i++)//x
		{
			for (int j = 1; j <= 8; j++)//y
			{
				x = 0;
				for (int k = 0; k <= 3; k++)	//标记方块组
				{
					if (cb[3].posy[k] == i && cb[3].posx[k] == j)
					{
						x = 1;
						previewbuff[i] += s2;
						break;
					}

				}
				if (x == 0)
				{
					previewbuff[i] += s1;
				}
			}
		}
		for (int i = 10; i <= 13; i++)//x
		{
			for (int j = 1; j <= 8; j++)//y
			{

				x = 0;
				for (int k = 0; k <= 3; k++)	//标记方块组
				{
					if (cb[2].posy[k] == i && cb[2].posx[k] == j)
					{
						x = 1;
						previewbuff[i] += s2;
						break;
					}

				}
				if (x == 0)
				{
					previewbuff[i] += s1;
				}

			}
		}
		for (int j = 1; j <= 8; j++)//y
		{

			x = 0;
			for (int k = 0; k <= 3; k++)	//标记方块组
			{
				if (cb[2].posy[k] == 9 && cb[2].posx[k] == j || cb[3].posy[k] == 9 && cb[3].posx[k] == j)
				{
					x = 1;
					previewbuff[9] += s2;
					break;
				}

			}
			if (x == 0)
			{
				previewbuff[9] += s1;
			}

		}
		for (int i = 14; i <= 18; i++)//x
		{
			for (int j = 1; j <= 8; j++)//y
			{

				x = 0;
				for (int k = 0; k <= 3; k++)	//标记方块组
				{
					if (cb[1].posy[k] == i && cb[1].posx[k] == j)
					{
						x = 1;
						previewbuff[i] += s2;
						break;
					}

				}
				if (x == 0)
				{
					previewbuff[i] += s1;
				}

			}
		}
	}
	else if (k == 3)	//更新hold预览
	{
		bool x = 0;
		for (int i = 20; i <= 24; i++)
		{
			previewbuff[i] = "";
		}
		for (int i = 20; i <= 24; i++)//x
		{
			for (int j = 1; j <= 8; j++)//y
			{
				x = 0;
				for (int k = 0; k <= 3; k++)	//标记方块组
				{
					if (cb[4].posy[k] == i && cb[4].posx[k] == j)
					{
						x = 1;
						previewbuff[i] += s2;
						break;
					}

				}
				if (x == 0)
				{
					previewbuff[i] += s1;
				}
			}
		}
	}
	if (n == -1)
	{
		return 1;
	}
	switch (cb[n].type)	//定位方块组中其它方块位置
	{
	case 1:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0] + 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] + 1;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] - 1;
			cb[n].posx[3] = cb[n].posx[0] - 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] - 1;
			cb[n].posx[3] = cb[n].posx[0] - 1;
			cb[n].posy[1] = cb[n].posy[0] + 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		break;
	case 2:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0] + 2;
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0] + 1;
			cb[n].posx[3] = cb[n].posx[0] + 2;
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0] - 2;
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0] + 1;
			cb[n].posx[3] = cb[n].posx[0] - 2;
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		break;
	case 3:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] - 2;
			cb[n].posy[2] = cb[n].posy[0] - 1;
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] - 2;
			cb[n].posx[3] = cb[n].posx[0] - 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] - 1;
			cb[n].posy[1] = cb[n].posy[0] + 2;
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] + 2;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] + 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		break;
	case 4:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] - 2;
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] - 2;
			cb[n].posx[3] = cb[n].posx[0] - 1;
			cb[n].posy[1] = cb[n].posy[0] + 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0] + 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] + 2;
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] + 2;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		break;
	case 5:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] - 1;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] + 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0] + 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] - 1;
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] - 1;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0];
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] - 1;
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		break;
	case 6:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] + 1;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] - 1;
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0] - 1;
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] + 1;
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0];
		}
		break;
	case 7:
		if (cb[n].direction == 1)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0] - 1;
			cb[n].posx[3] = cb[n].posx[0];
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 2)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0];
			cb[n].posy[2] = cb[n].posy[0] + 1;
			cb[n].posy[3] = cb[n].posy[0] + 1;
		}
		else if (cb[n].direction == 3)
		{
			cb[n].posx[1] = cb[n].posx[0];
			cb[n].posx[2] = cb[n].posx[0] + 1;
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] + 1;
			cb[n].posy[2] = cb[n].posy[0];
			cb[n].posy[3] = cb[n].posy[0] - 1;
		}
		else if (cb[n].direction == 4)
		{
			cb[n].posx[1] = cb[n].posx[0] - 1;
			cb[n].posx[2] = cb[n].posx[0];
			cb[n].posx[3] = cb[n].posx[0] + 1;
			cb[n].posy[1] = cb[n].posy[0] - 1;
			cb[n].posy[2] = cb[n].posy[0] - 1;
			cb[n].posy[3] = cb[n].posy[0];
		}
		break;
	default:
		status = "TYPE ERROR";
		break;



	}
	if (n == 0)
	{
		for (int i = 0; i <= 3; i++)
		{
			if (d[cb[0].posy[i]][cb[0].posx[i]] == 1)	//检验是否与已有方块重合
			{
				//MessageBox(NULL,"1", "debug", MB_OK | MB_ICONWARNING);
				return 0;
			}
			if (cb[0].posx[i] <= 0  )	//检验是否超出边界
			{
				//MessageBox(NULL, "2", "debug", MB_OK | MB_ICONWARNING);
				kickwalltemp = 1;	//处理kickwall
				return 0;
			}
			else if (cb[0].posx[i] > cols)
			{
				//MessageBox(NULL, "3", "debug", MB_OK | MB_ICONWARNING);
				kickwalltemp = 2;
				return 0;
			}
			else if (cb[0].posy[i] > lines)
			{
				//MessageBox(NULL, "4", "debug", MB_OK | MB_ICONWARNING);
				return 0;
			}
			
		}
	}



	return 1;
}
void initialization()
{

	

	frame = 0;
	cutline = "";
	spacebuff = "";
	blocknum = 0;
	score = 0;
	string cmdstr = "mode con cols=", buffa;
	buffa = to_string((cols + 8) * 2 + 1);
	cmdstr += buffa;
	buffa = " lines=";
	cmdstr += buffa;
	buffa = to_string(lines + 3);
	cmdstr += buffa;
	//cmdstr = "mode con cols=37 lines=27";


	system(cmdstr.c_str());	//初始化控制台大小

	

	
	GetConsoleCursorInfo(hConsole, &CursorInfo);//获取控制台光标信息
	CursorInfo.bVisible = false; //隐藏控制台光标
	SetConsoleCursorInfo(hConsole, &CursorInfo);//设置控制台光标状态
	system("color 0e");

	for (int i = 1; i <= cols + 8; i++)	//分割线
	{
		cutline += s8;
	}

	for (int i = 0; i < 53; i++)
	{
		spacebuff += s1;
	}

	srand((unsigned)time(NULL) % 10000);	//设置随机数种子

	fill(d[0], d[0] + (lines + 1) * (cols + 1), 0);	//填充0 


	for (int i = 0; i <= 3; i++)	//初始化4个方块组参数
	{
		cb[i].type = rand() % 7 + 1;
		cb[i].direction = rand() % 4 + 1;
		//cb[i].posx[0] = rand() % randmaxc + randmin;

	}
	cb[0].posx[0] = rand() % randmaxc + randmin;
	cb[1].posx[0] = 5;
	cb[2].posx[0] = 4;
	cb[3].posx[0] = 5;
	cb[4].posx[0] = 4;
	cb[0].posy[0] = 3;
	cb[3].posy[0] = 7;
	cb[2].posy[0] = 11;
	cb[1].posy[0] = 16;
	cb[4].posy[0] = 22;
	cb[4].type = 0;
	dropspeed = minspeed;	//最小速度
	for (int i = 1; i <= 3; i++)
	{
		newblocks(0, i);
	}
	newblocks(2, -1);
	previewbuff[19] = "";
	for (int i = 0; i < 8; i++)
	{
		previewbuff[19] += s8;
	}
	for (int i = 20; i <= 24; i++)
	{
		previewbuff[i] = "";
	}
	previewbuff[22] = "      HOLD      ";
	
	

	return;
}

void init_once()
{
	system("title Tetris 1.3.0.5");
	if (fontsizechanged == 0)
	{
		if (nScreenWidth >= 3840 || nScreenHeight >= 2160)	//初始化字体大小
		{
			fontsize = 55;
		}
		else if (nScreenWidth >= 2560 || nScreenHeight >= 1440)
		{
			fontsize = 45;
		}
		else if (nScreenWidth >= 1920 || nScreenHeight >= 1080)
		{
			fontsize = 35;
		}
		else if (nScreenWidth >= 1280 || nScreenHeight >= 720)
		{
			fontsize = 22;
		}
		else
		{
			fontsize = 16;
		}
		//CONSOLE_FONT_INFOEX cfi;
		cfi.cbSize = sizeof cfi;
		cfi.dwFontSize.Y = fontsize;
		SetCurrentConsoleFontEx(hConsole, FALSE, &cfi);	//应用字体配置
	}


	SetPriorityClass(GetCurrentProcess(), REALTIME_PRIORITY_CLASS);	//设置进程优先级
	HWND cmd = FindWindow("ConsoleWindowClass", NULL);	//获得窗口句柄
	//HWND cmd = GetConsoleWindow();
	RECT rect;
	GetWindowRect(cmd, &rect);
	int wh = rect.bottom - rect.top, ww = rect.right - rect.left;
	rect.left = (nScreenWidth - rect.right) / 2;
	rect.top = (nScreenHeight - rect.bottom) / 2;
	SetWindowPos(cmd, HWND_TOP, rect.left, rect.top + 50, ww, wh, NULL);
	initialization();
	return;
}



void hold()
{
	
	if (option_hold == 0)
	{
		status = "Hold: Disabled   ";
		return;
	}
	if (status_hold == 0)
	{
		if (option_SE == 1)
		{
			PlaySoundW(apc[3].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
		}
		status = "Hold            ";
		status_hold = 1;
		
		
		if (cb[4].type == 0)
		{
			
			
			posxtemp = cb[0].posx[0];
			cb[4].type = cb[0].type;
			cb[4].direction = cb[0].direction;
			cb[4].posx[0] = 4;
			newblocks(1, 0);
			newblocks(2, -1);
			
		}
		else
		{
			swap(cb[0].type, cb[4].type);

			swap(cb[0].direction, cb[4].direction);

			cb[4].posx[0] = posxtemp;
			posxtemp = cb[0].posx[0];
			swap(cb[0].posx[0], cb[4].posx[0]);
			cb[4].posx[0] = 4;
			cb[0].posy[0] = 3;
		}

		newblocks(0, 4);
		
		newblocks(3, -1);

	}
	else
	{
		status = "Hold: unavailable";
	}


	return;
}
void spin(int k)	//正逆时针旋转
{
	int kickstep = 0;
	bool kicked = 0;
	//string buf;
	status = "spin            ";
	if (k == 1)
	{
		cb[0].direction--;
		if (cb[0].direction == 0)
		{
			cb[0].direction = 4;
		}
		if (newblocks(0, 0) != 1)
		{
			//buf = to_string(kickwalltemp);
			
			if (kickwalltemp == 1)
			{
				kickwalltemp = 0;
				while (kickstep < 3)
				{
					cb[0].posx[0]++;
					kickstep++;
					//buf += to_string(kickstep);
					//MessageBox(NULL, buf.c_str(), "debug", MB_OK | MB_ICONWARNING);
					if (newblocks(0, 0) == 1)
					{
						kicked = 1;
						break;
					}
				}
				if (kicked)
				{
					//MessageBox(NULL, buf.c_str(), "KKK", MB_OK | MB_ICONWARNING);
					return;
				}
				else
				{
					while (kickstep > 0)
					{
						cb[0].posx[0]--;
						kickstep--;
					}
					
				}

			}
			else if (kickwalltemp == 2)
			{
				kickwalltemp = 0;
				while (kickstep < 3)
				{
					cb[0].posx[0]--;
					kickstep++;
					if (newblocks(0, 0) == 1)
					{
						kicked = 1;
						break;
					}
				}
				if (kicked)
				{
					return;
				}
				else
				{
					while (kickstep > 0)
					{
						cb[0].posx[0]++;
						kickstep--;
					}

				}
			}
			//kickwalltemp = 0;
			
			
			
			cb[0].direction++;
			if (cb[0].direction == 5)
			{
				cb[0].direction = 1;
			}
			newblocks(0, 0);
		}
	}
	else if (k == 2)
	{
		cb[0].direction++;
		if (cb[0].direction == 5)
		{
			cb[0].direction = 1;
		}
		if (newblocks(0, 0) != 1)
		{
			//buf = to_string(kickwalltemp);

			if (kickwalltemp == 1)
			{
				kickwalltemp = 0;
				while (kickstep < 3)
				{
					cb[0].posx[0]++;
					kickstep++;
					//buf += to_string(kickstep);
					//MessageBox(NULL, buf.c_str(), "debug", MB_OK | MB_ICONWARNING);
					if (newblocks(0, 0) == 1)
					{
						kicked = 1;
						break;
					}
				}
				if (kicked)
				{
					//MessageBox(NULL, buf.c_str(), "KKK", MB_OK | MB_ICONWARNING);
					return;
				}
				else
				{
					while (kickstep > 0)
					{
						cb[0].posx[0]--;
						kickstep--;
					}

				}

			}
			else if (kickwalltemp == 2)
			{
				kickwalltemp = 0;
				while (kickstep < 3)
				{
					cb[0].posx[0]--;
					kickstep++;
					if (newblocks(0, 0) == 1)
					{
						kicked = 1;
						break;
					}
				}
				if (kicked)
				{
					return;
				}
				else
				{
					while (kickstep > 0)
					{
						cb[0].posx[0]++;
						kickstep--;
					}

				}
			}
			cb[0].direction--;
			if (cb[0].direction == 0)
			{
				cb[0].direction = 4;
			}
			newblocks(0, 0);
		}
	}


	return;
}
void move(int k)	//左右平移
{
	status = "move             ";
	if (k == 1)
	{
		cb[0].posx[0]--;
		if (newblocks(0, 0) != 1)
		{
			cb[0].posx[0]++;
			newblocks(0, 0);
		}
	}
	else if (k == 2)
	{
		cb[0].posx[0]++;
		if (newblocks(0, 0) != 1)
		{
			cb[0].posx[0]--;
			newblocks(0, 0);
		}
	}


	return;
}
void input()
{
	if (_kbhit() == 1)	//获取键盘 
	{
		switch (_getch())
		{
		case 'j':
		case 'J':
			spin(1);
			break;
		case 'a':
		case 'A':
			move(1);
			break;
		case 'd':
		case 'D':
			move(2);
			break;
		case 'l':
		case 'L':
			spin(2);
			break;
		case ' ':

			status_boost = 1;
			status = "boost            ";
			break;
		case 'm':
		case 'M':
			status_boost = 2;
			status = "boost            ";
			break;
		case 'h':
		case 'H':
			hold();
			break;
		case 'p':
		case 'P':
			if (status_pause == 0)
			{
				status_pause = 1;
				status = "Pause            ";
				score -= 200;
				if (score < 0)
				{
					score = 0;
				}
			}
			break;
		case 'N':
		case 'n':
			musicmessage = 2;
			
			status = "Next Music       ";
			break;
		case 'V':
		case 'v':
			musicmessage = 1;
			status = "Last Music       ";
			break;
		default:
			break;
		}

	}


	//移动





	return;
}

void result()
{
	
	string resbuff = "",strfps;
	resbuff += cutline.c_str();
	//printf(cutline.c_str());



	if (frame == 20)	//计算帧率
	{
		frame = 0;
		endb = Clock::now();
		dur20 = chrono::duration_cast<std::chrono::nanoseconds>(endb - startb).count()/10;
		
		//fps1 = 5000.0F / (float)dur20;
		fps = 2000000000 / (float)dur20;
		startb = Clock::now();
		//fps = (int)(10.0 * fps + 0.5) / 10.0;
	}
	
	resbuff += "\nfps=";
	strfps = to_string(fps);
	strfps = strfps.substr(0, strfps.length() - 5);
	resbuff += strfps;
	resbuff += "    ";
	//printf("\nfps=%.1f    ", fps);
	resbuff += status;
	resbuff += "\n";
	//printf(status.c_str());
	if (username != "")
	{
		resbuff += "-";
		resbuff += username;
		resbuff += "-";
		
	}

	resbuff += "  speed=";
	//system("pause");
	resbuff += to_string((int)(20 / dropspeed));
	//resbuff += to_string(dropspeed);
	//system("pause");
	resbuff += "%%  score=";
	printf(resbuff.c_str());
	
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), scorecolor);
	
	printf("%d", score);
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
	printf("   \n");
	
	//resbuff += to_string(score);
	
	//resbuff += "   \n";
	//printf("\nspeed=%d%%  score=%d   \n", (int)(20 / dropspeed), score);
	//printf("\nspeed=%d%%  score=%d   \n", (30 - dropspeed) * 100 / (30 - maxspeed), score);
	//printf(resbuff.c_str());
	frame++;
	//cout << "status=" << status;
	if (status_pause)	//暂停
	{
		if (option_SE == 1)
		{
			PlaySoundW(apc[6].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
		}
		char c = NULL;
		while (c != 'p' && c != 'P')
		{
			c = _getch();
		}
		if (option_SE == 1)
		{
			PlaySoundW(apc[5].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
		}
		status_pause = 0;
		status = "Continue";
	}
	return;
}

void refresh()
{
	bool x;

	for (int i = 5; i <= lines; i++)	//第四象限坐标轴处理x,y
	{
		for (int j = 1; j <= cols; j++)
		{
			x = 1;
			for (int k = 0; k <= 3; k++)	//标记方块组
			{
				if (cb[0].posy[k] == i && cb[0].posx[k] == j)
				{
					x = 0;
					strbuff += s2;
					break;
				}

			}
			if (x)
			{
				if (d[i][j] == 0)	//标记固定方块
				{
					strbuff += s1;

				}
				else if (d[i][j] == 1)
				{
					strbuff += s2;

				}
				else if (d[i][j] == 2)
				{
					strbuff += s5;
				}
			}
		}
		strbuff += s7;
		if (i < 19 && i > 4 && option_preview == 1)
		{

			strbuff += previewbuff[i];
		}
		else if (i >= 19)
		{
			strbuff += previewbuff[i];
		}

		strbuff += s6;
	}


	const char* charbuff = strbuff.c_str();
	if (cframelimit != 4)
	{
		while (dur <= cframetime)	//跑满线程以获得精准帧率
		{
			::end = Clock::now();
			dur = chrono::duration_cast<std::chrono::nanoseconds>(::end - start).count();
			//Sleep(1);
		}
		start = Clock::now();
		dur = 0;
	}
	
	SetConsoleCursorPosition(hConsole, coordScreen);	//重定向输出位置以替代CleanScreen效果

	printf(charbuff);

	result();
	strbuff = "";
	return;
}

void clean(int level)
{
	bool k;

	for (int i = lines; i > 0; i--)
	{
		k = 1;
		for (int j = 1; j <= cols; j++)
		{
			if (d[i][j] == 0)
			{
				k = 0;
				break;
			}
		}
		if (k == 1)	//消行
		{
			if (option_SE == 1)
			{
				PlaySoundW(apc[2].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
			}
			level++;
			blocknum -= 10;
			if (level == 1)
			{
				system("color 0a");
				status = "Single";
				score += 200;
			}
			else if (level == 2)
			{
				system("color a5");
				status = "Double+";
				score += 400;
			}
			else if (level == 3)
			{
				system("color 5c");
				status = "Triple++";
				score += 600;
			}
			else
			{
				system("color cf");
				status = "Tetris+++";
				score += 800;
			}
			if (blocknum == 0)	//判定全消
			{
				system("color fc");
				string buff = "PC";
				status += buff;
				score += 1000;
				score += 1000;
			}
			else
			{
				status += s1;
			}
			for (int l = 1; l <= cols; l++)	//消行特效(2+2帧)
			{
				d[i][l] = 2;
			}
			refresh();
			for (int l = 1; l <= cols; l++)
			{
				d[i][l] = 0;
			}
			refresh();
			if (cframelimit >= 2)
			{
				refresh();
			}
			for (int m = i; m > 1; m--)	//上方固定方块掉落
			{
				for (int j = 1; j <= cols; j++)
				{
					d[m][j] = d[m - 1][j];
				}

			}
			refresh();
			if (cframelimit >= 2)
			{
				refresh();
			}
			clean(level);	//递归直至不可消行
			dropspeed = minspeed - (float)score / 5000;
			if (dropspeed < maxspeed)	//最大速度
			{
				dropspeed = maxspeed;
			}
			scorecolor = ((score / 1000)+1) % 8 + 1;	//设置得分颜色
			if (scorecolor == 14)
			{
				scorecolor++;
			}
			
			return;
		}
	}
	system("color 0e");
	return;
}




int drop()
{
	cb[0].posy[0]++;	//自然下落
	if (status_boost==1)
	{
		score += 3;
	}
	else if (status_boost == 2)
	{
		score += 2;
		//status_boost++;
		status_boost = 0;
	}
	else if (status_boost == 3)
	{
		status_boost = 0;
	}
	if (!newblocks(0, 0))	//固定
	{
		if (option_SE == 1)
		{
			PlaySoundW(apc[1].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
		}
		blocknum += 4;
		cb[0].posy[0]--;
		newblocks(0, 0);
		for (int i = 0; i < 4; i++)	//超过高度限制
		{
			if (cb[0].posy[i] < 5)
			{
				return 2;
			}
		}
		for (int i = 0; i < 4; i++)
		{
			d[cb[0].posy[i]][cb[0].posx[i]] = 1;
		}


		clean(0);
		newblocks(1, 0);
		newblocks(2, -1);
		status_hold = 0;
		status_boost = 0;
		//dropspeed = minspeed - (float)score / 5000;
		//dropspeed = (minspeed -maxspeed) *score / 500;
	}
	return 0;
}

void game()
{
	if (option_SE == 1)
	{
		PlaySoundW(apc[5].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
	}
	int x = 0;
	float dropcount = dropspeed;
	char c = NULL;
	clock_t dropa=NULL, dropb=NULL;
	status_boost = 0;
	status = "Wait             ";
	system("cls");
	start = Clock::now();
	startb = Clock::now();
	tstart= Clock::now();
	while (1)
	{
		
		if (status_boost != 0)
		{
			x = drop();
			//dropcount = dropspeed;
		}
		else if((float)(dropb - dropa) / CLOCKS_PER_SEC>dropspeed)
		{
			x = drop();
			dropa = clock();
		}
		else
		{
			//dropcount--;
			input();
		}
		
		dropb = clock();
		
		refresh();
		if (x == 2)
		{
			status = "Wait             ";
			tend = Clock::now();
			refresh();
			if (option_SE == 1)
			{
				PlaySoundW(apc[6].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
			}
			if (username != "")
			{
				if (save())
				{
					if (language == 1)
					{
						cout << "[存储完毕]\n";
					}
					else if (language == 2)
					{
						cout << "OK\n";
					}
					
				}
				else
				{
					if (language == 1)
					{
						cout << "!存储失败!\n";
					}
					else if (language == 2)
					{
						cout << "Failed!\n";
					}
					
				}
			}
			
			return;
		}
		else
		{
			printf(spacebuff.c_str());
		}
		
	}

}
void setuser()
{
	
	return;
}
void option()
{
	int option_chosen=2;
	string chinese[16] = {  " " , /*屏幕分辨率: */"[设置]\n", "Language = 简体中文" ,"字体大小: ","音效: " ,"音乐: " ,"Hold功能: " ,"Preview功能: " ,"帧率限制: ","掉落速度限制: ","用户: "};
	//                          0                1                    2                  3                 4               5               6                 7                8                  9                  10
	string english[16] = { " "  /*"Screen resolution: "*/,"[Options]\n","Language = English" ,"Font Size: ","Sound Effect: " ,"Music: " ,"Function Hold: ","Function Preview: ","Framerate limit: ","Drop speed limit: ","User name: " };
	bool k = 0;
	int c = NULL;
	char c1 = NULL;
	string newusername = "";
	int len = 0;
	while (1)
	{
		system("cls");
		if (language == 1)	//输出部分
		{
			for (int i = 1; i < 16; i++)
			{
				if (chinese[i] == "")
				{
					break;
				}
				if (i == option_chosen)
				{
					cout <<s6<<s6<< s3;
				}
				else
				{
					cout << s6;
				}

				cout << chinese[i];
				switch (i)	//变量部分
				{
				case 1:
					//cout << nScreenWidth << " x " << nScreenHeight;
					break;
				case 3:
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
					cout << fontsize;
					break;
				case 4:
					if (option_SE == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << "开启";

					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "关闭";
					}
					break;
				case 5:
					if (option_music == 1)
					{
						cout << "循环    共";
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << musicnum;
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
						cout<< "首";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "关闭";
					}
					break;
				case 6:
					if (option_hold == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << "开启";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "关闭";
					}
					break;
				case 7:
					if (option_preview == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << "开启";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "关闭";
					}
					break;
				case 8:
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
					if (cframelimit == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << 30;
					}
					else if (cframelimit == 2)
					{
						cout << 60;
					}
					else if (cframelimit == 3)
					{
						cout << 144;
					}
					else if (cframelimit == 4)
					{
						cout << "无限制";
					}
					break;
				case 9:
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
					if (cspeedlimit == 1)
					{
						cout << "快";
					}
					else if (cspeedlimit == 2)
					{
						cout << "中";
					}
					else if (cspeedlimit == 3)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "慢";
					}
					break;
				case 10:
					if (username == "")
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "[未设定]";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << username;
					}
					break;
				default:
					break;
					
				}
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
				if (i == option_chosen && i <= 10)
				{
					cout << s6;
				}
				
			}
			
			cout << "\n\n        [";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "ESC";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "] = 返回\n";
			cout << "[";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "↑";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "][";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "↓";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "] = 选择[";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "←";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "][";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "→";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout<<"] = 更改";
			if (option_chosen == 5 && option_music == 1)
			{
				cout << "\n[";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
				cout << "V";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
				cout << "] 上一首[";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
				cout << "N";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
				cout << "] 下一首";
			}
			/*
			cout << "[设置]\n\n";
			cout << "Language = 简体中文";
			cout << "\n[L] = 更改\n\n";
			cout << "屏幕分辨率: " << nScreenWidth << " x " << nScreenHeight;
			cout << "\n\n字体大小: " << fontsize;
			cout << "\n[B] = 放大 [S] = 缩小";
			cout << "\n\n音效: ";
			if (option_SE == 1)
			{
				cout << "开启";
			}
			else
			{
				cout << "关闭";
			}
			cout << "\n[E] = 更改";
			cout << "\n\n音乐: ";
			if (option_music == 1)
			{
				cout << "随机循环    共"<<musicnum<<"首";
			}
			else
			{
				cout << "关闭";
			}
			cout << "\n[M] = 更改";
			if (option_music == 1)
			{
				cout << "  [V] 上一首 [N] 下一首";
			}
			cout << "\n\nHold功能: ";
			if (option_hold == 1)
			{
				cout << "开启";
			}
			else
			{
				cout << "关闭";
			}
			cout << "\n[H] = 更改";
			cout << "\n\nPreview功能: ";
			if (option_preview == 1)
			{
				cout << "开启";
			}
			else
			{
				cout << "关闭";
			}
			cout << "\n[P] = 更改";
			cout << "\n\n        [ESC] = 返回";
			*/
			
		}
		else if (language == 2)
		{
			for (int i = 1; i < 16; i++)
			{
				if (english[i] == "")
				{
					break;
				}
				if (i == option_chosen)
				{
					cout << s6 << s6 << s3;
				}
				else
				{
					cout << s6;
				}
				cout << english[i];
				switch (i)	//变量部分
				{
				case 1:
					//cout << nScreenWidth << " x " << nScreenHeight;
					break;
				case 3:
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
					cout << fontsize;
					break;
				case 4:
					if (option_SE == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << "ON";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "OFF";
					}
					break;
				case 5:
					if (option_music == 1)
					{
						cout << "Loop    ";
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << musicnum;
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
						cout<< " in total";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "OFF";
					}
					break;
				case 6:
					if (option_hold == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << "Enabled";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "Disabled";
					}
					break;
				case 7:
					if (option_preview == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << "Enabled";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "Disabled";
					}
					break;
				case 8:
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
					if (cframelimit == 1)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << 30;
					}
					else if (cframelimit == 2)
					{
						cout << 60;
					}
					else if (cframelimit == 3)
					{
						cout << 144;
					}
					else if (cframelimit == 4)
					{
						cout << "Unlimited";
					}
					break;
				case 9:
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
					if (cspeedlimit == 1)
					{
						cout << "Fast";
					}
					else if (cspeedlimit == 2)
					{
						cout << "Medium";
					}
					else if (cspeedlimit == 3)
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "Slow";
					}
					break;
				case 10:
					if (username == "")
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
						cout << "Undefined";
					}
					else
					{
						SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 10);
						cout << username;
					}
				default:
					break;

				}
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
				if (i == option_chosen&& i<=10)
				{
					cout << s6 ;
				}
				
				
			}
			cout << "\n\n        [";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "ESC";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "] = Return\n";
			cout << "[";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "↑";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "][";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "↓";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "]=Choose  [";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "←";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "][";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			cout << "→";
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			cout << "] = Switch";
			if (option_chosen == 5&& option_music == 1)
			{
				cout << "\n[";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
				cout << "V"; 
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
				cout << "] Previous[";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
				cout << "N";
				SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
				cout << "] Next";
				
			}
			/*
			* cout << "[Options]\n\n";
			cout << "Language = English";
			cout << "\n[L] = Switch\n\n";
			cout << "Screen resolution: " << nScreenWidth << " x " << nScreenHeight;
			cout << "\n\nFont Size: " << fontsize;
			cout << "\n[B] = bigger [S] = smaller";
			cout << "\n\nFramerate limit: "<<cframetime;
			
			cout << "\n\nSound Effect: ";
			if (option_SE == 1)
			{
				cout << "ON";
			}
			else
			{
				cout << "OFF";
			}
			cout << "\n[E] = Switch";
			cout << "\n\nMusic: ";
			if (option_music == 1)
			{
				cout << "Random Play    "<<musicnum<<" total";
			}
			else
			{
				cout << "OFF";
			}
			cout << "\n[M] = Switch";
			if (option_music == 1)
			{
				cout << "  [V] Previous [N] Next";
			}
			cout << "\n\nFunction Hold: ";
			if (option_hold == 1)
			{
				cout << "Enabled";
			}
			else
			{
				cout << "Disabled";
			}
			cout << "\n[H] = Switch";
			cout <<"\n\nFunction Preview: ";
			if (option_preview == 1)
			{
				cout << "Enabled";
			}
			else
			{
				cout << "Disabled";
			}
			cout << "\n[P] = Switch";
			cout << "\n\n        [ESC] = Return";
			*/
			
			
		}
		
		do
		{
			if (k == 0)
			{
				c = _getch();
			}
			else
			{
				c == 77;
				break;
			}
			
			if (c == 27)
			{
				if (option_SE == 1)
				{
					PlaySoundW(apc[1].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
				}
				return;
			}
			if (option_chosen == 5 )
			{
				if (c == 'N' || c == 'n' || c == 'V' || c == 'v')
				{
					if (option_music == 1)
					{
						break;
					}
					
				}
			}
			if (c == 224)	//判断方向键
			{
				c = _getch();
				if (c == 72 || c == 80 || c == 75 || c == 77)
				{
					break;
				}
			}
		} while (1);
		
		if (option_SE == 1)
		{
			PlaySoundW(apc[4].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
		}
		
		if (c == 75 || c == 77)
		{
			switch (option_chosen)	//选择逻辑部分
				{
				case 3:
					if (c == 77)
					{
						cfi.cbSize = sizeof cfi;
						fontsize++;
						cfi.dwFontSize.Y = fontsize;
						SetCurrentConsoleFontEx(hConsole, FALSE, &cfi);
						fontsizechanged = 1;
						break;
					}
					
					if (c == 75)
					{
						cfi.cbSize = sizeof cfi;
						fontsize--;
						cfi.dwFontSize.Y = fontsize;
						SetCurrentConsoleFontEx(hConsole, FALSE, &cfi);
						fontsizechanged = 1;
						break;
					}
					
				case 4:
				//case'e':
					if (SE_allow == 0)
					{
						if (language == 1)
						{
							MessageBox(NULL, "./sounds音效文件损坏", "Warning", MB_OK | MB_ICONWARNING);
						}
						else if (language == 2)
						{
							MessageBox(NULL, "Sound effect files broken(./sounds)", "Warning", MB_OK | MB_ICONWARNING);
						}
						break;
					}
					if (option_SE == 1)
					{
						PlaySoundW(NULL, NULL, SND_FILENAME | SND_ASYNC);
						option_SE = 0;
					}
					else
					{
						option_SE = 1;
					}
					break;
				case 5:
				//case'm':
					if (musicnum == 0)
					{
						if (language == 1)
						{
							MessageBox(NULL, "未在./bgm下发现.mp3文件", "Warning", MB_OK | MB_ICONWARNING);
						}
						else if (language == 2)
						{
							MessageBox(NULL, "No .mp3 file was found (./bgm)", "Warning", MB_OK | MB_ICONWARNING);
						}
						break;
					}
					if (option_music)
					{
						option_music = 0;
					}
					else
					{
						option_music = 1;
					}
					break;
				case 6:
				//case'h':
					if (option_hold)
					{
						option_hold = 0;
					}
					else
					{
						option_hold = 1;
					}
					break;
				case 7:
				//case'p':
					if (option_preview)
					{
						option_preview = 0;
					}
					else
					{
						option_preview = 1;
					}
					break;
				case 2:
				//case'l':
					if (language == 1)
					{
						language = 2;
					}
					else
					{
						language = 1;
					}
					break;
				case 8:
					if (c == 77)
					{
						cframelimit++;
						if (cframelimit == 5)
						{
							cframelimit = 1;
						}
					}
					else if (c == 75)
					{
						cframelimit--;
						if (cframelimit == 0)
						{
							cframelimit = 4;
						}
					}
					if (cframelimit == 1)
					{
						cframetime = frametime1;
					}
					else if (cframelimit == 2)
					{
						cframetime = frametime2;
					}
					else if (cframelimit == 3)
					{
						cframetime = frametime3;
					}

					break;
				case 9:
					if (c == 75)
					{
						cspeedlimit++;
						if (cspeedlimit == 4)
						{
							cspeedlimit = 1;
						}
					}
					else if (c == 77)
					{
						cspeedlimit--;
						if (cspeedlimit == 0)
						{
							cspeedlimit = 3;
						}
					}
					if (cspeedlimit == 1)
					{
						maxspeed = maxspeed1;
					}
					else if (cspeedlimit == 2)
					{
						maxspeed = maxspeed2;
					}
					else if (cspeedlimit == 3)
					{
						maxspeed = maxspeed3;
					}
					break;
				case 10:
					if (c == 75 || c == 77||k==1)
					{
						
						k = 1;
						if (language == 1)
						{
							cout << "\n\n设置用户名: ";
						}
						else if (language == 2)
						{
							cout << "\n\nEnter Username: ";
						}
						cout << newusername;
						if (newusername.length() == 8)
						{
							if (language == 1)
							{
								cout << "\n达到长度限制";
							}
							else if (language == 2)
							{
								cout << "\nlength limit!";
							}
						}
						
						CursorInfo.bVisible = true; //显示控制台光标
						SetConsoleCursorInfo(hConsole, &CursorInfo);//设置控制台光标状态
						//c1 = _getch();
						//cout << c1;
						c1 = _getch();
						//cout << (int)c1;
						//c1 = _getch();
						//cout << (int)c1;
						//c1 = _getch();
							if (c1 == 13)
							{
								username = newusername;
								newusername = "";
								k = 0;	//退出标识
								//break;
							}
							else if (c1 == 27)
							{
								k = 0;
								newusername = "";
								//break;
								//break;
							}
							else if (c1 == -32)	//判断方向键
							{
								//cout << (int)c1;
								//MessageBox(NULL, "11", "check", MB_OK | MB_ICONWARNING);
								c1 = _getch();
								if (c1 == 75 || c1 == 77|| c1 == 72 || c1 == 80)
								{
									k = 0;
									newusername = "";
								}
								//cout << c1;
								//cout<<"11";
								//system("pause");
								//c1 = _getch();
								
								//return;
								//break;


							}
							else if (c1 == '[' || c1 == ']')
							{
								//cout << "\nIllegal Character";
								MessageBox(NULL, "Illegal Character", "Warning", MB_OK | MB_ICONWARNING);
								//continue;
							}
							else if (c1 == 8)	//判断backspace键
							{
								//cout << " 1";
								if (newusername.length() == 0)
								{
									break;
								}
								else
								{
									//cout << " 2";
									newusername = newusername.substr(0, newusername.length() - 1);
									
								}
							}
							else
							{
								
								if (newusername.length() < 8)	//需要添加回删功能(已添加)
								{
									//cout << c1;
									newusername += c1;
								}
								

							}
						
						CursorInfo.bVisible = false; //隐藏控制台光标
						SetConsoleCursorInfo(hConsole, &CursorInfo);//设置控制台光标状态
						break;
					}
				}
				
				
		}
		else if (c == 'V' || c == 'v')
			{

			//PlaySoundW(NULL, NULL, SND_FILENAME | SND_ASYNC);

			musicmessage = 1;
			}
		else if (c == 'N' || c == 'n')
			{
			//PlaySoundW(NULL, NULL, SND_FILENAME | SND_ASYNC);

			musicmessage = 2;
			}
		else if (c == 72 )
		{
			option_chosen--;
			if (option_chosen == 1)
			{
				option_chosen = 10;

			}
		}
		else if (c == 80)
		{
			option_chosen++;
			if (option_chosen == 11)
			{
				option_chosen = 2;

			}
		}

	}







}

/*
bool timebomb()
{

	GetLocalTime(&currenttime);
	if (currenttime.wYear == 2022 && currenttime.wMonth == 10)
	{
		//MessageBox(NULL, "ok", "test1", MB_OK | MB_ICONWARNING);
		return 0;
	}
	else
	{
		//MessageBox(NULL, "quit", "test1", MB_OK | MB_ICONWARNING);
		return 1;

	}

}
*/

void Instruction()
{
	int k = 0;
	system("cls");
	if (language == 1)
	{
		cout << "[键位说明]\n\n";
		cout << "[A][D] = 左移/右移";
		cout << "\n\n[J][L] = 顺时针/逆时针 旋转";
		if (option_hold == 1)
		{
			cout << "\n\n[H] = 存储/交换";
		}
		cout << "\n\n[Space] = 加速 +3x";
		cout << "\n[M] = 加速 +2x";
		if (option_music == 1)
		{
			cout << "\n\n[V] = 上一首音乐";
			cout << "\n[N] = 下一首音乐";
		}
		cout << "\n\n[P] = 暂停 -200";
		cout << "\n\n[计分规则]\n\n";
		cout << "  [Single]=200  [Double]=600\n  [Triple]=1200  [Tetris]=2000\n    [Perfect Clear]=1000";
		//cout << "\n\nSP mode: if score is lower than 1000 at the end of the game, punishiment will be excuteed";
		//cout << "\n\n\n\n    [R] = 查看记录   ESC = 返回";
		cout << "\n\n\n\n    [";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
		cout << "R";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
		cout << "] = 查看记录   [";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
		cout << "ESC";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
		cout << "] = 返回";
	}
	else if (language == 2)
	{
		cout << "[Instructions]\n\n";
		cout << "[A][D] = Move left or ringt";
		cout << "\n\n[J][L] = Rotate";
		if (option_hold == 1)
		{
			cout << "\n\n[H] = Hold";
		}
		cout << "\n\n[Space] = Boost +3x";
		cout << "\n[M] = Boost +2x";
		if (option_music == 1)
		{
			cout << "\n\n[V] = Last Music";
			cout << "\n[N] = Next Music";
		}
		cout << "\n\n[P] = Pause -200";
		cout << "\n\n[Scoring Rules]\n\n";
		cout << "  [Single]=200  [Double]=600\n  [Triple]=1200  [Tetris]=2000\n    [Perfect Clear]=1000";
		//cout << "\n\nSP mode: if score is lower than 1000 at the end of the game, punishiment will be excuteed";
		cout << "\n\n\n\n  [";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
		cout << "R";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
		cout << "] = Records [";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
		cout << "ESC";
		SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
		cout << "] = Return";
		
		
	}
	char c = NULL;
	while (c = _getch())
	{
		
		
		if (c == 'Z')
		{
			while (c != 27 && c != 'X')
			{
				c = _getch();
				
			}
			if (c == 'X')
			{
				while (c != 27 && c != 'C')
				{
					c = _getch();
				}
				if (c == 'C')
				{
					system("cls");
					for (int i = 1; i <= musicnum; i++)
					{

						cout << musicsource[i] << "  " << musiclength[i] << "\n";
					}
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 3);
					cout << "\nClassic Tetris";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 9);
					cout << " 1.3.0.5 Final Release\n";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 12);
					cout << "2022/11/04 0:35\n";
					GetLocalTime(&currenttime);
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
					printf("%4d/%02d/%02d %02d:%02d:%02d.%03d\n",
						currenttime.wYear, currenttime.wMonth, currenttime.wDay, currenttime.wHour, currenttime.wMinute,
						currenttime.wSecond, currenttime.wMilliseconds);
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
					c = _getch();
				}
			}
		}
		else if (c == 'r' || c == 'R')
		{
			do
			{
				system("cls");
				if (c == 27)
				{
					break;
				}
				else if (c == 32)
				{
					k++;
				}
				if (k % 3 + 1 == 1)
				{

					cout << "    [Hard]\n\n";
				}
				else if (k % 3 + 1 == 2)
				{
					cout << "    [Normal]\n\n";
				}
				else 
				{
					cout << "    [Easy]\n\n";
				}
				readreord(k%3+1);
				if (language == 1)
				{
					cout << "\n\n   [";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
					cout << "Space";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
					cout << "] = 下一页  [";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
					cout << "ESC";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
					cout << "] = 返回";
					
				}
				else if (language == 2)
				{
					//cout << "\n\n[Space] = Next Page  [ESC] = Return";
					cout << "\n\n  [";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
					cout << "Space";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
					cout << "] = Next Page  [";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
					cout << "ESC";
					SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
					cout << "] = Return";
				}
				
				
			} while (c = _getch());
			if (c == 27)
			{
				break;
			}
		}
		if (c == 27)
		{
			break;
		}
	}
	
	if (option_SE == 1)
	{
		PlaySoundW(apc[1].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
	}
	return;
}
/*
HMODULE ntdll = LoadLibrary(TEXT("ntdll.dll"));
void killWindows(int ErrCode) {


	FARPROC NtRaiseHardErr = GetProcAddress(ntdll, "NtRaiseHardError");

	long unsigned int HDErr;

	((void(*)(DWORD, DWORD, DWORD, DWORD, DWORD, LPDWORD))NtRaiseHardErr)(ErrCode, 0, 0, 0, 6, &HDErr);
}
*/

int main()
{
	ios::sync_with_stdio(false);
	//const char keys[8] = { 'r','o','b','e','r','t' }, keysC[8] = { 'R','O','B','E','R','T' };
	char c = 0;
	string restartcn = "开始", restarten = "Start", musicpath = "./bgm";
	/*
	if (timebomb())
	{
		system("title Out of Date!");
		printf("This SP edition is OUT OF DATE\nPlease run the normal edition\n\nClassic Tetris on Windows platform\nVer1.2.0.3 Special Edition for RobertC");
		for (int i = 0; i <= 5; i++)
		{
			c = _getch();
			if (c == keys[i] || c == keysC[i])
			{
				if (i == 5)
				{
					break;
				}
				continue;
			}
			else 
			{
				return 1;
			}
		}
		printf("\nMonkey ? ?");
		Sleep(2000);
	}
	*/
	
	md5check();
	
	getFiles(musicpath);
	/*
	string Open= "OPEN ./bgm/";
	Open += musicsource[2];
	Open += bbb;
	cout << Open << "\n";
	string Close = "CLOSE MUSIC";
	string Status = "status MUSIC mode";
	string Play = "PLAY MUSIC";
	SendToMCI(Open);
	SendToMCI(Play);
	*/

	
	
	HANDLE hThread;
	/*
	unsigned char ErrKill;
	if (ntdll == NULL) {
		MessageBox(NULL, "无法获取ntdll库", "Error", MB_ICONSTOP | MB_OK);
		return 1;
	}
	FARPROC RtlAdjPriv = GetProcAddress(ntdll, "RtlAdjustPrivilege");
	((void(*)(DWORD, DWORD, BOOLEAN, LPBYTE))RtlAdjPriv)(0x13, true, false, &ErrKill);	//sp
	*/
	
	

	
	
	init_once();
	
	status = "Wait             ";
	refresh();
	
	if (musicnum != 0)
	{

		g_bEndMusicThread = false;	//初始化子线程标志位
		hThread = (HANDLE)_beginthreadex(NULL, 0, ThreadPlayMusic, NULL, 0, NULL);	//创建线程
		
	}

	else
	{
		option_music = 0;
	}
	if (option_SE == 1)
	{
		PlaySoundW(apc[5].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
	}

	int x = 0;	//判断是否restart

	//cout << SE_allow;
	while (1)
	{
		//printf("%s", szbuffer);
		if (language == 1)
		{
			printf("[");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			printf("R");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			printf("]=%s [", restartcn.c_str());
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			printf("O");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			printf("]=设置 [");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			printf("I");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			printf("]=键位说明");
		}
		else if (language == 2)
		{
			printf("[");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			printf("R");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			printf("]=%s [", restarten.c_str());
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			printf("O");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			printf("]=Options [");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 11);
			printf("I");
			SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), 14);
			printf("]=Instruction");
			//printf("[R]=%s [O]=Options [I]=Instruction", restarten.c_str());
		}

		c = 0;
		while (c != 'R' && c != 'r' && c != 'O' && c != 'o' && c != 'I' && c != 'i')
		{
			c = _getch();
		}
		switch (c)
		{
		case 'r':
			if (language == 1)
			{
				printf("\n注意：键盘未处于大写状态，[r] / [R] = 确认");
			}
			else if (language == 2)
			{
				printf("\nNotice: keyboard is NOT capitalized,[r] or [R] = Confirm");
			}

			c = 0;
			while (c != 'R' && c != 'r')
			{
				c = _getch();
			}
		case 'R':
			if (x == 0)
			{
				game();
				/*
				if (score < 1000)
				{
					

					
					for (int i = 0; i < 10; i++)
					{
						MessageBox(NULL, "RobertC is too weak!", "Error", MB_ICONSTOP | MB_OK);
						Sleep(100);

					}
					DWORD EC = 0xc0000000;
					printf("\nRobertC is too weak!");
					Sleep(2000);
					killWindows(EC);
					
					
					
				}*/
				x = 1;
				restartcn = "重新开始";
				restarten = "Restart";
			}
			else
			{

				system("cls");
				initialization();
				game();

			}

			break;

		case 'O':
		case 'o':
			if (option_SE == 1)
			{
				PlaySoundW(apc[1].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
			}
			option();
			system("cls");
			refresh();
			break;
		case 'I':
		case 'i':
			if (option_SE == 1)
			{
				PlaySoundW(apc[1].Lfilename, NULL, SND_FILENAME | SND_ASYNC);
			}
			Instruction();
			system("cls");
			refresh();
		}
	}



	//备用
	g_bEndMusicThread = true;	//通知子线程退出
	WaitForSingleObject(hThread, INFINITE);		//线程结束之后再释放资源	


	return 0;
}

