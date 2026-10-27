/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4418 : Family 9 := level9.get ⟨642,by decide⟩
def sourceMap4418 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4418 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4418_checked : acceptsGraphIso
    (source (graph core4418) (root 9) 2 2) DegreeTwoThreeSpectrum4945.graph sourceMap4418=true := by decide +kernel
theorem fusedMap4418_checked : acceptsGraphIso
    (fused (graph core4418) (root 9) 2 2) DegreeTwoThreeSpectrum4414.graph fusedMap4418=true := by decide +kernel
theorem certified4418 : Certified (graph core4418) (root 9) 2 2 :=
  of_native_maps core4418 DegreeTwoThreeSpectrum4945.graph DegreeTwoThreeSpectrum4414.graph
    sourceMap4418 fusedMap4418 sourceMap4418_checked fusedMap4418_checked
    DegreeTwoThreeFiniteComparisons.comparison4418
#print axioms sourceMap4418_checked
#print axioms fusedMap4418_checked
#print axioms certified4418
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
