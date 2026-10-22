/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5391 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap5391 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5391 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5391_checked : acceptsGraphIso
    (source (graph core5391) (root 6) 4 4) DegreeTwoThreeSpectrum7050.graph sourceMap5391=true := by decide +kernel
theorem fusedMap5391_checked : acceptsGraphIso
    (fused (graph core5391) (root 6) 4 4) DegreeTwoThreeSpectrum5015.graph fusedMap5391=true := by decide +kernel
theorem certified5391 : Certified (graph core5391) (root 6) 4 4 :=
  of_native_maps core5391 DegreeTwoThreeSpectrum7050.graph DegreeTwoThreeSpectrum5015.graph
    sourceMap5391 fusedMap5391 sourceMap5391_checked fusedMap5391_checked
    DegreeTwoThreeFiniteComparisons.comparison5391
#print axioms sourceMap5391_checked
#print axioms fusedMap5391_checked
#print axioms certified5391
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
