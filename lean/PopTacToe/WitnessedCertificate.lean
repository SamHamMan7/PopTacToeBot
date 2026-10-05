import PopTacToe.ForceWinEquivariance

namespace PopTacToe

def VerifiedStates (fuel : Nat) (states : Array State) : Prop :=
  ∀ (state : State), state ∈ states → BlueForcesWithin fuel state

def VerifiedLookup (fuel : Nat) (lookup : Nat → Option State) : Prop :=
  ∀ (index : Nat) (state : State),
    lookup index = some state → BlueForcesWithin fuel state

def VerifiedChunks (fuel : Nat)
    (chunks : Array (Nat → Option State)) : Prop :=
  ∀ (lookup : Nat → Option State), lookup ∈ chunks → VerifiedLookup fuel lookup

def chunkedLookup (chunks : Array (Nat → Option State))
    (chunkSize index : Nat) : Option State :=
  if chunkSize = 0 then
    none
  else
    match chunks[index / chunkSize]? with
    | none => none
    | some lookup => lookup (index % chunkSize)

inductive ChildWitness where
  | terminal
  | known (index : Nat) (symmetry : TorusSymmetry)
  deriving BEq, DecidableEq, Repr

inductive NodeWitness where
  | blue (target : Square) (child : ChildWitness)
  | red (replies : Array (Option ChildWitness))
  deriving Repr

structure WitnessedEntry where
  state : State
  witness : NodeWitness
  deriving Repr

structure PackedBlueEntry where
  blue : Nat
  red : Nat
  moveCode : Nat
  deriving Repr

def d4OfNat : Nat → D4
  | 0 => .identity
  | 1 => .rotate90
  | 2 => .rotate180
  | 3 => .rotate270
  | 4 => .mirror
  | 5 => .mirrorRotate90
  | 6 => .mirrorRotate180
  | _ => .mirrorRotate270

def unpackSymmetry (code : Nat) : TorusSymmetry :=
  {
    shape := d4OfNat ((code / 64) % 8)
    rowShift := Fin.ofNat 8 ((code / 8) % 8)
    columnShift := Fin.ofNat 8 (code % 8)
  }

def unpackChild (code : Nat) : ChildWitness :=
  if code = 0 then
    .terminal
  else
    let payload := code - 1
    .known (payload / 512) (unpackSymmetry (payload % 512))

def unpackBlueEntry (blueBin redBin : Nat)
    (packed : PackedBlueEntry) : WitnessedEntry :=
  {
    state := {
      blue := BitVec.ofNat 64 packed.blue
      red := BitVec.ofNat 64 packed.red
      blueBin := blueBin
      redBin := redBin
      turn := .blue
    }
    witness := .blue
      (Fin.ofNat 64 (packed.moveCode % 64))
      (unpackChild (packed.moveCode / 64))
  }

def unpackBlueEntries (blueBin redBin : Nat)
    (packed : Array PackedBlueEntry) : Array WitnessedEntry :=
  packed.map (unpackBlueEntry blueBin redBin)

def unpackBlueStates (blueBin redBin : Nat)
    (packed : Array PackedBlueEntry) : Array State :=
  packed.map fun entry => (unpackBlueEntry blueBin redBin entry).state

def witnessedEntriesLookup (entries : Array WitnessedEntry)
    (index : Nat) : Option State :=
  match entries[index]? with
  | none => none
  | some entry => some entry.state

def packedBlueEntriesLookup (blueBin redBin : Nat)
    (packed : Array PackedBlueEntry) (index : Nat) : Option State :=
  match packed[index]? with
  | none => none
  | some entry => some (unpackBlueEntry blueBin redBin entry).state

def packedWordBase : Nat := Nat.shiftLeft 1 64

def packedBlueNatEntryAt (data index : Nat) : PackedBlueEntry :=
  let shifted := Nat.shiftRight data (192 * index)
  let afterBlue := Nat.shiftRight shifted 64
  let afterRed := Nat.shiftRight afterBlue 64
  {
    blue := shifted % packedWordBase
    red := afterBlue % packedWordBase
    moveCode := afterRed % packedWordBase
  }

def packedBlueNatLookup (blueBin redBin count data index : Nat) : Option State :=
  if index < count then
    some (unpackBlueEntry blueBin redBin
      (packedBlueNatEntryAt data index)).state
  else
    none

def childCheck (known : Nat → Option State)
    (state : State) (target : Square) : ChildWitness → Bool
  | .terminal => decide (BlueWins (applyPlacement state target))
  | .known index symmetry =>
      match known index with
      | none => false
      | some knownState =>
          decide
            (transformState symmetry (applyPlacement state target) = knownState)

def ChildCertified (known : Nat → Option State)
    (state : State) (target : Square) (witness : ChildWitness) : Prop :=
  childCheck known state target witness = true

instance (known : Nat → Option State)
    (state : State) (target : Square) (witness : ChildWitness) :
    Decidable (ChildCertified known state target witness) := by
  unfold ChildCertified
  infer_instance

def ReplyCertified (known : Nat → Option State)
    (state : State) (replies : Array (Option ChildWitness))
    (target : Square) : Prop :=
  match replies[target.val]? with
  | some (some child) => ChildCertified known state target child
  | _ => False

instance (known : Nat → Option State)
    (state : State) (replies : Array (Option ChildWitness))
    (target : Square) :
    Decidable (ReplyCertified known state replies target) := by
  unfold ReplyCertified
  cases replies[target.val]? with
  | none => infer_instance
  | some reply =>
      cases reply <;> infer_instance

def WitnessedLocalCertificate
    (known : Nat → Option State) (entry : WitnessedEntry) : Prop :=
  outcome entry.state = .ongoing ∧ 0 < entry.state.moverBin ∧
    match entry.witness with
    | .blue target child =>
        entry.state.turn = .blue ∧
          LegalPlacement entry.state target ∧
            ChildCertified known entry.state target child
    | .red replies =>
        entry.state.turn = .red ∧
          ∀ target : Square,
            LegalPlacement entry.state target →
              ReplyCertified known entry.state replies target

instance (known : Nat → Option State)
    (entry : WitnessedEntry) :
    Decidable (WitnessedLocalCertificate known entry) := by
  rcases entry with ⟨state, witness⟩
  cases witness <;> unfold WitnessedLocalCertificate <;> dsimp <;>
    infer_instance

def witnessedLocalCheck (known : Nat → Option State)
    (entry : WitnessedEntry) : Bool :=
  decide (WitnessedLocalCertificate known entry)

theorem childCertified_sound {fuel : Nat}
    {known : Nat → Option State} {state : State} {target : Square}
    {witness : ChildWitness}
    (knownSound : VerifiedLookup fuel known)
    (certified : ChildCertified known state target witness) :
    BlueForcesWithin fuel (applyPlacement state target) := by
  cases witness with
  | terminal =>
      apply blueWins_forcesWithin fuel
      exact of_decide_eq_true
        (by simpa [ChildCertified, childCheck] using certified)
  | known index symmetry =>
      unfold ChildCertified childCheck at certified
      cases knownEquation : known index with
      | none => simp [knownEquation] at certified
      | some knownState =>
          simp only [knownEquation] at certified
          have transformedEquals :
              transformState symmetry (applyPlacement state target) =
                knownState :=
            of_decide_eq_true certified
          apply (blueForcesWithin_transform_iff symmetry).mp
          rw [transformedEquals]
          exact knownSound index knownState knownEquation

theorem witnessedLocalCheck_sound {fuel : Nat}
    {known : Nat → Option State} {entry : WitnessedEntry}
    (checked : witnessedLocalCheck known entry = true)
    (knownSound : VerifiedLookup fuel known) :
    BlueForcesWithin (fuel + 1) entry.state := by
  have valid : WitnessedLocalCertificate known entry :=
    of_decide_eq_true (by simpa [witnessedLocalCheck] using checked)
  rcases entry with ⟨state, witness⟩
  rcases valid with ⟨ongoing, placementPhase, nodeValid⟩
  unfold BlueForcesWithin
  refine Or.inr ⟨ongoing, placementPhase, ?_⟩
  cases witness with
  | blue target child =>
      rcases nodeValid with ⟨blueTurn, legal, childValid⟩
      rw [blueTurn]
      exact ⟨target, legal, childCertified_sound knownSound childValid⟩
  | red replies =>
      rcases nodeValid with ⟨redTurn, allReplies⟩
      rw [redTurn]
      intro target legal
      have childValid := allReplies target legal
      unfold ReplyCertified at childValid
      cases replyEquation : replies[target.val]? with
      | none => simp [replyEquation] at childValid
      | some reply =>
          cases reply with
          | none => simp [replyEquation] at childValid
          | some child =>
              simp only [replyEquation] at childValid
              exact childCertified_sound knownSound childValid

def witnessedEntriesCheck (known : Nat → Option State)
    (entries : Array WitnessedEntry) : Bool :=
  entries.toList.all (witnessedLocalCheck known)

def packedBlueEntriesCheck (known : Nat → Option State) (blueBin redBin : Nat)
    (packed : Array PackedBlueEntry) : Bool :=
  packed.toList.all fun entry =>
    witnessedLocalCheck known (unpackBlueEntry blueBin redBin entry)

def packedBlueNatEntriesCheck (known : Nat → Option State)
    (blueBin redBin count data : Nat) : Bool :=
  (List.range count).all fun index =>
    witnessedLocalCheck known
      (unpackBlueEntry blueBin redBin (packedBlueNatEntryAt data index))

theorem witnessedEntriesCheck_sound {fuel : Nat}
    {known : Nat → Option State} {entries : Array WitnessedEntry}
    (checked : witnessedEntriesCheck known entries = true)
    (knownSound : VerifiedLookup fuel known)
    {entry : WitnessedEntry} (member : entry ∈ entries) :
    BlueForcesWithin (fuel + 1) entry.state := by
  apply witnessedLocalCheck_sound (knownSound := knownSound)
  have allChecked :
      entries.toList.all (witnessedLocalCheck known) = true := by
    simpa only [witnessedEntriesCheck] using checked
  exact List.all_eq_true.mp allChecked entry member.val

def entryStates (entries : Array WitnessedEntry) : Array State :=
  entries.map WitnessedEntry.state

theorem witnessedEntriesCheck_verified {fuel : Nat}
    {known : Nat → Option State} {entries : Array WitnessedEntry}
    (checked : witnessedEntriesCheck known entries = true)
    (knownSound : VerifiedLookup fuel known) :
    VerifiedStates (fuel + 1) (entryStates entries) := by
  unfold VerifiedStates
  intro state member
  rcases Array.mem_map.mp member with
    ⟨entry, entryMember, stateEquation⟩
  rw [← stateEquation]
  exact witnessedEntriesCheck_sound checked knownSound entryMember

theorem packedBlueEntriesCheck_verified {fuel blueBin redBin : Nat}
    {known : Nat → Option State} {packed : Array PackedBlueEntry}
    (checked : packedBlueEntriesCheck known blueBin redBin packed = true)
    (knownSound : VerifiedLookup fuel known) :
    VerifiedStates (fuel + 1) (unpackBlueStates blueBin redBin packed) := by
  unfold VerifiedStates
  intro state member
  rcases Array.mem_map.mp member with
    ⟨entry, entryMember, stateEquation⟩
  rw [← stateEquation]
  apply witnessedLocalCheck_sound (knownSound := knownSound)
  have allChecked :
      packed.toList.all
        (fun packedEntry => witnessedLocalCheck known
          (unpackBlueEntry blueBin redBin packedEntry)) = true := by
    simpa only [packedBlueEntriesCheck] using checked
  exact List.all_eq_true.mp allChecked entry entryMember.val

theorem witnessedEntriesCheck_lookup_verified {fuel : Nat}
    {known : Nat → Option State} {entries : Array WitnessedEntry}
    (checked : witnessedEntriesCheck known entries = true)
    (knownSound : VerifiedLookup fuel known) :
    VerifiedLookup (fuel + 1) (witnessedEntriesLookup entries) := by
  unfold VerifiedLookup
  intro index state found
  unfold witnessedEntriesLookup at found
  cases entryEquation : entries[index]? with
  | none => simp [entryEquation] at found
  | some entry =>
      simp only [entryEquation] at found
      have stateEquation : entry.state = state := Option.some.inj found
      rw [← stateEquation]
      exact witnessedEntriesCheck_sound checked knownSound
        (Array.mem_iff_getElem?.2 ⟨index, entryEquation⟩)

theorem packedBlueEntriesCheck_lookup_verified {fuel blueBin redBin : Nat}
    {known : Nat → Option State} {packed : Array PackedBlueEntry}
    (checked : packedBlueEntriesCheck known blueBin redBin packed = true)
    (knownSound : VerifiedLookup fuel known) :
    VerifiedLookup (fuel + 1)
      (packedBlueEntriesLookup blueBin redBin packed) := by
  unfold VerifiedLookup
  intro index state found
  unfold packedBlueEntriesLookup at found
  cases entryEquation : packed[index]? with
  | none => simp [entryEquation] at found
  | some entry =>
      simp only [entryEquation] at found
      have stateEquation :
          (unpackBlueEntry blueBin redBin entry).state = state :=
        Option.some.inj found
      rw [← stateEquation]
      apply witnessedLocalCheck_sound (knownSound := knownSound)
      have allChecked :
          packed.toList.all
            (fun packedEntry => witnessedLocalCheck known
              (unpackBlueEntry blueBin redBin packedEntry)) = true := by
        simpa only [packedBlueEntriesCheck] using checked
      exact List.all_eq_true.mp allChecked entry
        (Array.mem_iff_getElem?.2 ⟨index, entryEquation⟩).val

theorem packedBlueNatEntriesCheck_lookup_verified
    {fuel blueBin redBin count data : Nat}
    {known : Nat → Option State}
    (checked :
      packedBlueNatEntriesCheck known blueBin redBin count data = true)
    (knownSound : VerifiedLookup fuel known) :
    VerifiedLookup (fuel + 1)
      (packedBlueNatLookup blueBin redBin count data) := by
  unfold VerifiedLookup
  intro index state found
  unfold packedBlueNatLookup at found
  split at found
  · rename_i inRange
    have stateEquation :
        (unpackBlueEntry blueBin redBin
          (packedBlueNatEntryAt data index)).state = state :=
      Option.some.inj found
    rw [← stateEquation]
    apply witnessedLocalCheck_sound (knownSound := knownSound)
    have allChecked :
        (List.range count).all (fun candidate =>
          witnessedLocalCheck known
            (unpackBlueEntry blueBin redBin
              (packedBlueNatEntryAt data candidate))) = true := by
      simpa only [packedBlueNatEntriesCheck] using checked
    exact List.all_eq_true.mp allChecked index (List.mem_range.mpr inRange)
  · simp_all

theorem verifiedStates_append {fuel : Nat} {left right : Array State}
    (leftVerified : VerifiedStates fuel left)
    (rightVerified : VerifiedStates fuel right) :
    VerifiedStates fuel (left ++ right) := by
  unfold VerifiedStates at leftVerified rightVerified ⊢
  intro state member
  have side : state ∈ left ∨ state ∈ right := by
    simpa using member
  cases side with
  | inl inLeft => exact leftVerified state inLeft
  | inr inRight => exact rightVerified state inRight

theorem verifiedChunks_single {fuel : Nat} {lookup : Nat → Option State}
    (verified : VerifiedLookup fuel lookup) :
    VerifiedChunks fuel #[lookup] := by
  unfold VerifiedChunks
  intro candidate member
  have equality : candidate = lookup := by
    simpa using member
  rw [equality]
  exact verified

theorem verifiedChunks_append {fuel : Nat}
    {left right : Array (Nat → Option State)}
    (leftVerified : VerifiedChunks fuel left)
    (rightVerified : VerifiedChunks fuel right) :
    VerifiedChunks fuel (left ++ right) := by
  unfold VerifiedChunks at leftVerified rightVerified ⊢
  intro lookup member
  have side : lookup ∈ left ∨ lookup ∈ right := by
    simpa using member
  cases side with
  | inl inLeft => exact leftVerified lookup inLeft
  | inr inRight => exact rightVerified lookup inRight

theorem chunkedLookup_sound {fuel chunkSize index : Nat}
    {chunks : Array (Nat → Option State)} {state : State}
    (chunksVerified : VerifiedChunks fuel chunks)
    (found : chunkedLookup chunks chunkSize index = some state) :
    BlueForcesWithin fuel state := by
  unfold chunkedLookup at found
  split at found
  · simp_all
  · cases chunkEquation : chunks[index / chunkSize]? with
    | none => simp [chunkEquation] at found
    | some lookup =>
        simp only [chunkEquation] at found
        exact chunksVerified lookup
          (Array.mem_iff_getElem?.2 ⟨index / chunkSize, chunkEquation⟩)
          (index % chunkSize) state found

theorem chunkedLookup_verified {fuel chunkSize : Nat}
    {chunks : Array (Nat → Option State)}
    (chunksVerified : VerifiedChunks fuel chunks) :
    VerifiedLookup fuel (chunkedLookup chunks chunkSize) := by
  unfold VerifiedLookup
  intro index state found
  exact chunkedLookup_sound chunksVerified found

#print axioms childCertified_sound
#print axioms witnessedLocalCheck_sound
#print axioms witnessedEntriesCheck_sound
#print axioms witnessedEntriesCheck_verified
#print axioms packedBlueEntriesCheck_verified
#print axioms witnessedEntriesCheck_lookup_verified
#print axioms packedBlueEntriesCheck_lookup_verified
#print axioms packedBlueNatEntriesCheck_lookup_verified
#print axioms verifiedStates_append
#print axioms verifiedChunks_single
#print axioms verifiedChunks_append
#print axioms chunkedLookup_sound
#print axioms chunkedLookup_verified

end PopTacToe