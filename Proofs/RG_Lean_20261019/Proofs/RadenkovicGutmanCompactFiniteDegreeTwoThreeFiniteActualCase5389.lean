/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5389 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap5389 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5389 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5389_checked : acceptsGraphIso
    (source (graph core5389) (root 6) 4 4) DegreeTwoThreeSpectrum7048.graph sourceMap5389=true := by decide +kernel
theorem fusedMap5389_checked : acceptsGraphIso
    (fused (graph core5389) (root 6) 4 4) DegreeTwoThreeSpectrum4981.graph fusedMap5389=true := by decide +kernel
theorem certified5389 : Certified (graph core5389) (root 6) 4 4 :=
  of_native_maps core5389 DegreeTwoThreeSpectrum7048.graph DegreeTwoThreeSpectrum4981.graph
    sourceMap5389 fusedMap5389 sourceMap5389_checked fusedMap5389_checked
    DegreeTwoThreeFiniteComparisons.comparison5389
#print axioms sourceMap5389_checked
#print axioms fusedMap5389_checked
#print axioms certified5389
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
