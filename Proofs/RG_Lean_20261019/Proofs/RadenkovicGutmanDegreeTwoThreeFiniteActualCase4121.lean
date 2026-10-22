/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4121 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap4121 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,7,8,9,10] (sourceLabel 8 2 2 v)
def fusedMap4121 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4121_checked : acceptsGraphIso
    (source (graph core4121) (root 8) 2 2) DegreeTwoThreeSpectrum3611.graph sourceMap4121=true := by decide +kernel
theorem fusedMap4121_checked : acceptsGraphIso
    (fused (graph core4121) (root 8) 2 2) DegreeTwoThreeSpectrum2428.graph fusedMap4121=true := by decide +kernel
theorem certified4121 : Certified (graph core4121) (root 8) 2 2 :=
  of_native_maps core4121 DegreeTwoThreeSpectrum3611.graph DegreeTwoThreeSpectrum2428.graph
    sourceMap4121 fusedMap4121 sourceMap4121_checked fusedMap4121_checked
    DegreeTwoThreeFiniteComparisons.comparison4121
#print axioms sourceMap4121_checked
#print axioms fusedMap4121_checked
#print axioms certified4121
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
