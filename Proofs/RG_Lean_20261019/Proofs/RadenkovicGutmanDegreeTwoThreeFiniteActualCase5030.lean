/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5030 : Family 10 := level10.get ⟨1710,by decide⟩
def sourceMap5030 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5030 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5030_checked : acceptsGraphIso
    (source (graph core5030) (root 10) 2 2) DegreeTwoThreeSpectrum7631.graph sourceMap5030=true := by decide +kernel
theorem fusedMap5030_checked : acceptsGraphIso
    (fused (graph core5030) (root 10) 2 2) DegreeTwoThreeSpectrum6486.graph fusedMap5030=true := by decide +kernel
theorem certified5030 : Certified (graph core5030) (root 10) 2 2 :=
  of_native_maps core5030 DegreeTwoThreeSpectrum7631.graph DegreeTwoThreeSpectrum6486.graph
    sourceMap5030 fusedMap5030 sourceMap5030_checked fusedMap5030_checked
    DegreeTwoThreeFiniteComparisons.comparison5030
#print axioms sourceMap5030_checked
#print axioms fusedMap5030_checked
#print axioms certified5030
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
