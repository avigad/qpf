#exit
import data.finset
import data.fix.parser.equations

namespace queue

inductive c_type
| uint | array (t : c_type)

inductive cond
| full | empty


-- uint32_t buff_size;
-- uint32_t *buffer;
-- uint32_t fillIndex, useIndex, count = 0;
inductive vars
| buff_size | buffer
| fillIndex | useIndex | count

open c_type
def ty : vars → c_type
| vars.buff_size := uint
| vars.buffer := array uint
| vars.fillIndex := uint
| vars.useIndex := uint
| vars.count := uint

def idx : c_type → Type
| uint := unit
| (array uint) := ℕ
| (array t) := ℕ × idx t

codata process (α : Type) : Type
| acquire : process → process
| release : process → process
| wait : cond → process → process
| signal : cond → process → process
| read : Π v : vars, idx (ty v) → (unsigned → process) → process
| write : Π v : vars, idx (ty v) → unsigned → process → process
| pure : α → process

instance : monad process :=
sorry

structure state :=
(ι : Type)
(pcs : ι → process unit)
(cond : cond → finset ι)
(mem : ∀ var, idx (ty var) → unsigned)

end queue
