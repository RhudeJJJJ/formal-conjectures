/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4390 : Family 9 := level9.get ⟨573,by decide⟩
def sourceMap4390 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4390 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4390_checked : acceptsGraphIso
    (source (graph core4390) (root 9) 2 2) DegreeTwoThreeSpectrum4917.graph sourceMap4390=true := by decide +kernel
theorem fusedMap4390_checked : acceptsGraphIso
    (fused (graph core4390) (root 9) 2 2) DegreeTwoThreeSpectrum4222.graph fusedMap4390=true := by decide +kernel
theorem certified4390 : Certified (graph core4390) (root 9) 2 2 :=
  of_native_maps core4390 DegreeTwoThreeSpectrum4917.graph DegreeTwoThreeSpectrum4222.graph
    sourceMap4390 fusedMap4390 sourceMap4390_checked fusedMap4390_checked
    DegreeTwoThreeFiniteComparisons.comparison4390
#print axioms sourceMap4390_checked
#print axioms fusedMap4390_checked
#print axioms certified4390
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
