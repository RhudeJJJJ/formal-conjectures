/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4352 : Family 9 := level9.get ⟨479,by decide⟩
def sourceMap4352 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4352 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4352_checked : acceptsGraphIso
    (source (graph core4352) (root 9) 2 2) DegreeTwoThreeSpectrum4837.graph sourceMap4352=true := by decide +kernel
theorem fusedMap4352_checked : acceptsGraphIso
    (fused (graph core4352) (root 9) 2 2) DegreeTwoThreeSpectrum4521.graph fusedMap4352=true := by decide +kernel
theorem certified4352 : Certified (graph core4352) (root 9) 2 2 :=
  of_native_maps core4352 DegreeTwoThreeSpectrum4837.graph DegreeTwoThreeSpectrum4521.graph
    sourceMap4352 fusedMap4352 sourceMap4352_checked fusedMap4352_checked
    DegreeTwoThreeFiniteComparisons.comparison4352
#print axioms sourceMap4352_checked
#print axioms fusedMap4352_checked
#print axioms certified4352
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
