/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4293 : Family 9 := level9.get ⟨336,by decide⟩
def sourceMap4293 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4293 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4293_checked : acceptsGraphIso
    (source (graph core4293) (root 9) 2 2) DegreeTwoThreeSpectrum4701.graph sourceMap4293=true := by decide +kernel
theorem fusedMap4293_checked : acceptsGraphIso
    (fused (graph core4293) (root 9) 2 2) DegreeTwoThreeSpectrum4221.graph fusedMap4293=true := by decide +kernel
theorem certified4293 : Certified (graph core4293) (root 9) 2 2 :=
  of_native_maps core4293 DegreeTwoThreeSpectrum4701.graph DegreeTwoThreeSpectrum4221.graph
    sourceMap4293 fusedMap4293 sourceMap4293_checked fusedMap4293_checked
    DegreeTwoThreeFiniteComparisons.comparison4293
#print axioms sourceMap4293_checked
#print axioms fusedMap4293_checked
#print axioms certified4293
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
