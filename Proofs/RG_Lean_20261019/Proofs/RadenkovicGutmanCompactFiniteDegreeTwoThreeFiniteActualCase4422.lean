/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4422 : Family 9 := level9.get ⟨653,by decide⟩
def sourceMap4422 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4422 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4422_checked : acceptsGraphIso
    (source (graph core4422) (root 9) 2 2) DegreeTwoThreeSpectrum4949.graph sourceMap4422=true := by decide +kernel
theorem fusedMap4422_checked : acceptsGraphIso
    (fused (graph core4422) (root 9) 2 2) DegreeTwoThreeSpectrum4445.graph fusedMap4422=true := by decide +kernel
theorem certified4422 : Certified (graph core4422) (root 9) 2 2 :=
  of_native_maps core4422 DegreeTwoThreeSpectrum4949.graph DegreeTwoThreeSpectrum4445.graph
    sourceMap4422 fusedMap4422 sourceMap4422_checked fusedMap4422_checked
    DegreeTwoThreeFiniteComparisons.comparison4422
#print axioms sourceMap4422_checked
#print axioms fusedMap4422_checked
#print axioms certified4422
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
