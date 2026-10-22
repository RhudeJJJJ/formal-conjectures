/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4324 : Family 9 := level9.get ⟨410,by decide⟩
def sourceMap4324 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![5,0,1,2,3,4,12,13,14,15,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4324 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4324_checked : acceptsGraphIso
    (source (graph core4324) (root 9) 2 2) DegreeTwoThreeSpectrum4783.graph sourceMap4324=true := by decide +kernel
theorem fusedMap4324_checked : acceptsGraphIso
    (fused (graph core4324) (root 9) 2 2) DegreeTwoThreeSpectrum4377.graph fusedMap4324=true := by decide +kernel
theorem certified4324 : Certified (graph core4324) (root 9) 2 2 :=
  of_native_maps core4324 DegreeTwoThreeSpectrum4783.graph DegreeTwoThreeSpectrum4377.graph
    sourceMap4324 fusedMap4324 sourceMap4324_checked fusedMap4324_checked
    DegreeTwoThreeFiniteComparisons.comparison4324
#print axioms sourceMap4324_checked
#print axioms fusedMap4324_checked
#print axioms certified4324
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
