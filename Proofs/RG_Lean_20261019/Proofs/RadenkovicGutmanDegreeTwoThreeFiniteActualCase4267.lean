/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4267 : Family 9 := level9.get ⟨265,by decide⟩
def sourceMap4267 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4267 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4267_checked : acceptsGraphIso
    (source (graph core4267) (root 9) 2 2) DegreeTwoThreeSpectrum4876.graph sourceMap4267=true := by decide +kernel
theorem fusedMap4267_checked : acceptsGraphIso
    (fused (graph core4267) (root 9) 2 2) DegreeTwoThreeSpectrum4076.graph fusedMap4267=true := by decide +kernel
theorem certified4267 : Certified (graph core4267) (root 9) 2 2 :=
  of_native_maps core4267 DegreeTwoThreeSpectrum4876.graph DegreeTwoThreeSpectrum4076.graph
    sourceMap4267 fusedMap4267 sourceMap4267_checked fusedMap4267_checked
    DegreeTwoThreeFiniteComparisons.comparison4267
#print axioms sourceMap4267_checked
#print axioms fusedMap4267_checked
#print axioms certified4267
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
