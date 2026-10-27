/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4503 : Family 10 := level10.get ⟨298,by decide⟩
def sourceMap4503 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4503 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4503_checked : acceptsGraphIso
    (source (graph core4503) (root 10) 2 2) DegreeTwoThreeSpectrum6573.graph sourceMap4503=true := by decide +kernel
theorem fusedMap4503_checked : acceptsGraphIso
    (fused (graph core4503) (root 10) 2 2) DegreeTwoThreeSpectrum5470.graph fusedMap4503=true := by decide +kernel
theorem certified4503 : Certified (graph core4503) (root 10) 2 2 :=
  of_native_maps core4503 DegreeTwoThreeSpectrum6573.graph DegreeTwoThreeSpectrum5470.graph
    sourceMap4503 fusedMap4503 sourceMap4503_checked fusedMap4503_checked
    DegreeTwoThreeFiniteComparisons.comparison4503
#print axioms sourceMap4503_checked
#print axioms fusedMap4503_checked
#print axioms certified4503
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
