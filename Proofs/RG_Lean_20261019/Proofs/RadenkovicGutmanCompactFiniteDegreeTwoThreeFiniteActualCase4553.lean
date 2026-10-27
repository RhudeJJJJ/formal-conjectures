/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4553 : Family 10 := level10.get ⟨460,by decide⟩
def sourceMap4553 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,9,10,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4553 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4553_checked : acceptsGraphIso
    (source (graph core4553) (root 10) 2 2) DegreeTwoThreeSpectrum6827.graph sourceMap4553=true := by decide +kernel
theorem fusedMap4553_checked : acceptsGraphIso
    (fused (graph core4553) (root 10) 2 2) DegreeTwoThreeSpectrum5897.graph fusedMap4553=true := by decide +kernel
theorem certified4553 : Certified (graph core4553) (root 10) 2 2 :=
  of_native_maps core4553 DegreeTwoThreeSpectrum6827.graph DegreeTwoThreeSpectrum5897.graph
    sourceMap4553 fusedMap4553 sourceMap4553_checked fusedMap4553_checked
    DegreeTwoThreeFiniteComparisons.comparison4553
#print axioms sourceMap4553_checked
#print axioms fusedMap4553_checked
#print axioms certified4553
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
