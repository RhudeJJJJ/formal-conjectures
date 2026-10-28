/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5376 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5376 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 4 4 v)
def fusedMap5376 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 4 4 v)
theorem sourceMap5376_checked : acceptsGraphIso
    (source (graph core5376) (root 5) 4 4) DegreeTwoThreeSpectrum4658.graph sourceMap5376=true := by decide +kernel
theorem fusedMap5376_checked : acceptsGraphIso
    (fused (graph core5376) (root 5) 4 4) DegreeTwoThreeSpectrum3882.graph fusedMap5376=true := by decide +kernel
theorem certified5376 : Certified (graph core5376) (root 5) 4 4 :=
  of_native_maps core5376 DegreeTwoThreeSpectrum4658.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap5376 fusedMap5376 sourceMap5376_checked fusedMap5376_checked
    DegreeTwoThreeFiniteComparisons.comparison5376
#print axioms sourceMap5376_checked
#print axioms fusedMap5376_checked
#print axioms certified5376
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
