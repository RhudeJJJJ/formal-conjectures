/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5002 : Family 10 := level10.get ⟨1627,by decide⟩
def sourceMap5002 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5002 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5002_checked : acceptsGraphIso
    (source (graph core5002) (root 10) 2 2) DegreeTwoThreeSpectrum7603.graph sourceMap5002=true := by decide +kernel
theorem fusedMap5002_checked : acceptsGraphIso
    (fused (graph core5002) (root 10) 2 2) DegreeTwoThreeSpectrum6190.graph fusedMap5002=true := by decide +kernel
theorem certified5002 : Certified (graph core5002) (root 10) 2 2 :=
  of_native_maps core5002 DegreeTwoThreeSpectrum7603.graph DegreeTwoThreeSpectrum6190.graph
    sourceMap5002 fusedMap5002 sourceMap5002_checked fusedMap5002_checked
    DegreeTwoThreeFiniteComparisons.comparison5002
#print axioms sourceMap5002_checked
#print axioms fusedMap5002_checked
#print axioms certified5002
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
