/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4312 : Family 9 := level9.get ⟨383,by decide⟩
def sourceMap4312 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4312 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4312_checked : acceptsGraphIso
    (source (graph core4312) (root 9) 2 2) DegreeTwoThreeSpectrum4755.graph sourceMap4312=true := by decide +kernel
theorem fusedMap4312_checked : acceptsGraphIso
    (fused (graph core4312) (root 9) 2 2) DegreeTwoThreeSpectrum4323.graph fusedMap4312=true := by decide +kernel
theorem certified4312 : Certified (graph core4312) (root 9) 2 2 :=
  of_native_maps core4312 DegreeTwoThreeSpectrum4755.graph DegreeTwoThreeSpectrum4323.graph
    sourceMap4312 fusedMap4312 sourceMap4312_checked fusedMap4312_checked
    DegreeTwoThreeFiniteComparisons.comparison4312
#print axioms sourceMap4312_checked
#print axioms fusedMap4312_checked
#print axioms certified4312
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
