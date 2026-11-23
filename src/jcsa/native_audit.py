"""Optional batched reference checker; never selected by the frozen classifier.

Build with make jcsa-audit-engine. Unlike the planner's optimized mate
test this checker enumerates reference-engine legal moves directly throughout.
"""
import os
from pathlib import Path
import subprocess
from count.sampler import to_sfen
from plan.moves import usi_sq

DEFAULT=os.environ.get('CHU_NATIVE_AUDIT',str(Path(__file__).resolve().parents[2]/'out/bin/jcsa-native-audit'))


class NativeAudit:
    def __init__(self,path=None):
        if path is None:
            path = os.environ.get("CHU_NATIVE_AUDIT", DEFAULT)
        self.p=subprocess.Popen([path],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)

    def ask(self,command):
        if '\n' in command:raise ValueError('one protocol request required')
        self.p.stdin.write(command+'\n');self.p.stdin.flush()
        response=self.p.stdout.readline().rstrip('\n')
        kind,_,payload=response.partition('\t')
        if kind not in ('ok','fail'):raise ValueError('reference checker error: '+response)
        return kind=='ok',payload

    def mated(self,board,turn='B',flag=None):
        sfen=to_sfen(board,turn.lower(),usi_sq(flag) if flag else '-')
        ok,result=self.ask('mated\t'+sfen)
        if not ok or result not in ('0','1'):raise ValueError('invalid mate response')
        return result=='1'

    def view(self,board,turn='B',flag=None):
        sfen=to_sfen(board,turn.lower(),usi_sq(flag) if flag else '-')
        ok,result=self.ask('view\t'+sfen)
        terminal,_,moves=result.partition('\t')
        if not ok or terminal not in ('0','1'):raise ValueError('invalid state view')
        return terminal=='1',frozenset(moves.split())

    def verify(self,moves,target,stratum,flag=None):
        if stratum not in ('nonterm','flagsj','term'):raise ValueError('unknown stratum')
        if any(not isinstance(m,str) or any(c.isspace() for c in m) or not m for m in moves):
            raise ValueError('move strings must be nonempty protocol tokens')
        sfen=to_sfen(target,'b',usi_sq(flag) if flag else '-')
        if not moves:return self.ask('verify0\t'+stratum+'\t'+sfen+'\t0')
        return self.ask('verify\t'+stratum+'\t'+sfen+'\t'+str(len(moves))+'\t'+' '.join(moves))

    def close(self):
        if self.p.poll() is None:self.p.kill()
        self.p.wait()
