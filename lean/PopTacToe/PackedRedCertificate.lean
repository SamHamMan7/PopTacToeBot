import PopTacToe.WitnessedCertificate

namespace PopTacToe

def packedRedWordsPerEntry : Nat := 66

def packedRedNatWordAt (data entryIndex wordIndex : Nat) : Nat :=
  Nat.shiftRight data (64 * (packedRedWordsPerEntry * entryIndex + wordIndex)) %
    packedWordBase

def unpackRedReply (code : Nat) : Option ChildWitness :=
  if code = 0 then none else some (unpackChild (code - 1))

def packedRedNatStateAt (blueBin redBin data index : Nat) : State :=
  {
    blue := BitVec.ofNat 64 (packedRedNatWordAt data index 0)
    red := BitVec.ofNat 64 (packedRedNatWordAt data index 1)
    blueBin := blueBin
    redBin := redBin
    turn := .red
  }

def packedRedNatEntryAt (blueBin redBin data index : Nat) : WitnessedEntry :=
  {
    state := packedRedNatStateAt blueBin redBin data index
    witness := .red (Array.ofFn fun target : Fin 64 =>
      unpackRedReply (packedRedNatWordAt data index (target.val + 2)))
  }

def packedRedNatLookup (blueBin redBin count data index : Nat) : Option State :=
  if index < count then
    some (packedRedNatStateAt blueBin redBin data index)
  else
    none

def packedRedNatEntriesCheck (known : Nat → Option State)
    (blueBin redBin count data : Nat) : Bool :=
  (List.range count).all fun index =>
    witnessedLocalCheck known (packedRedNatEntryAt blueBin redBin data index)

theorem packedRedNatEntriesCheck_lookup_verified
    {fuel blueBin redBin count data : Nat}
    {known : Nat → Option State}
    (checked :
      packedRedNatEntriesCheck known blueBin redBin count data = true)
    (knownSound : VerifiedLookup fuel known) :
    VerifiedLookup (fuel + 1)
      (packedRedNatLookup blueBin redBin count data) := by
  unfold VerifiedLookup
  intro index state found
  unfold packedRedNatLookup at found
  split at found
  · rename_i inRange
    have stateEquation :
        (packedRedNatEntryAt blueBin redBin data index).state = state := by
      exact Option.some.inj found
    rw [← stateEquation]
    apply witnessedLocalCheck_sound (knownSound := knownSound)
    have allChecked :
        (List.range count).all (fun candidate =>
          witnessedLocalCheck known
            (packedRedNatEntryAt blueBin redBin data candidate)) = true := by
      simpa only [packedRedNatEntriesCheck] using checked
    exact List.all_eq_true.mp allChecked index (List.mem_range.mpr inRange)
  · simp_all

#print axioms packedRedNatEntriesCheck_lookup_verified

end PopTacToe