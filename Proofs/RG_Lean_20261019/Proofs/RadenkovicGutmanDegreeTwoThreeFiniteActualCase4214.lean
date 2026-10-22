/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4214 : Family 9 := level9.get ⟨102,by decide⟩
def sourceMap4214 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4214 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4214_checked : acceptsGraphIso
    (source (graph core4214) (root 9) 2 2) DegreeTwoThreeSpectrum4551.graph sourceMap4214=true := by decide +kernel
theorem fusedMap4214_checked : acceptsGraphIso
    (fused (graph core4214) (root 9) 2 2) DegreeTwoThreeSpectrum4091.graph fusedMap4214=true := by decide +kernel
theorem certified4214 : Certified (graph core4214) (root 9) 2 2 :=
  of_native_maps core4214 DegreeTwoThreeSpectrum4551.graph DegreeTwoThreeSpectrum4091.graph
    sourceMap4214 fusedMap4214 sourceMap4214_checked fusedMap4214_checked
    DegreeTwoThreeFiniteComparisons.comparison4214
#print axioms sourceMap4214_checked
#print axioms fusedMap4214_checked
#print axioms certified4214
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
