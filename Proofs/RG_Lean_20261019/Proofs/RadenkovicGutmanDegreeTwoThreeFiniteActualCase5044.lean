/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5044 : Family 10 := level10.get ⟨1746,by decide⟩
def sourceMap5044 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap5044 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5044_checked : acceptsGraphIso
    (source (graph core5044) (root 10) 2 2) DegreeTwoThreeSpectrum7645.graph sourceMap5044=true := by decide +kernel
theorem fusedMap5044_checked : acceptsGraphIso
    (fused (graph core5044) (root 10) 2 2) DegreeTwoThreeSpectrum6600.graph fusedMap5044=true := by decide +kernel
theorem certified5044 : Certified (graph core5044) (root 10) 2 2 :=
  of_native_maps core5044 DegreeTwoThreeSpectrum7645.graph DegreeTwoThreeSpectrum6600.graph
    sourceMap5044 fusedMap5044 sourceMap5044_checked fusedMap5044_checked
    DegreeTwoThreeFiniteComparisons.comparison5044
#print axioms sourceMap5044_checked
#print axioms fusedMap5044_checked
#print axioms certified5044
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
