/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5386 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap5386 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5386 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5386_checked : acceptsGraphIso
    (source (graph core5386) (root 6) 4 4) DegreeTwoThreeSpectrum7045.graph sourceMap5386=true := by decide +kernel
theorem fusedMap5386_checked : acceptsGraphIso
    (fused (graph core5386) (root 6) 4 4) DegreeTwoThreeSpectrum5087.graph fusedMap5386=true := by decide +kernel
theorem certified5386 : Certified (graph core5386) (root 6) 4 4 :=
  of_native_maps core5386 DegreeTwoThreeSpectrum7045.graph DegreeTwoThreeSpectrum5087.graph
    sourceMap5386 fusedMap5386 sourceMap5386_checked fusedMap5386_checked
    DegreeTwoThreeFiniteComparisons.comparison5386
#print axioms sourceMap5386_checked
#print axioms fusedMap5386_checked
#print axioms certified5386
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
