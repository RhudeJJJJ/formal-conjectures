/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4735 : Family 10 := level10.get ⟨963,by decide⟩
def sourceMap4735 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4735 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4735_checked : acceptsGraphIso
    (source (graph core4735) (root 10) 2 2) DegreeTwoThreeSpectrum7499.graph sourceMap4735=true := by decide +kernel
theorem fusedMap4735_checked : acceptsGraphIso
    (fused (graph core4735) (root 10) 2 2) DegreeTwoThreeSpectrum5875.graph fusedMap4735=true := by decide +kernel
theorem certified4735 : Certified (graph core4735) (root 10) 2 2 :=
  of_native_maps core4735 DegreeTwoThreeSpectrum7499.graph DegreeTwoThreeSpectrum5875.graph
    sourceMap4735 fusedMap4735 sourceMap4735_checked fusedMap4735_checked
    DegreeTwoThreeFiniteComparisons.comparison4735
#print axioms sourceMap4735_checked
#print axioms fusedMap4735_checked
#print axioms certified4735
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
