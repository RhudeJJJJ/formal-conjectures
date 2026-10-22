/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4378 : Family 9 := level9.get ⟨547,by decide⟩
def sourceMap4378 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4378 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4378_checked : acceptsGraphIso
    (source (graph core4378) (root 9) 2 2) DegreeTwoThreeSpectrum4905.graph sourceMap4378=true := by decide +kernel
theorem fusedMap4378_checked : acceptsGraphIso
    (fused (graph core4378) (root 9) 2 2) DegreeTwoThreeSpectrum4175.graph fusedMap4378=true := by decide +kernel
theorem certified4378 : Certified (graph core4378) (root 9) 2 2 :=
  of_native_maps core4378 DegreeTwoThreeSpectrum4905.graph DegreeTwoThreeSpectrum4175.graph
    sourceMap4378 fusedMap4378 sourceMap4378_checked fusedMap4378_checked
    DegreeTwoThreeFiniteComparisons.comparison4378
#print axioms sourceMap4378_checked
#print axioms fusedMap4378_checked
#print axioms certified4378
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
