/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5026 : Family 10 := level10.get ⟨1702,by decide⟩
def sourceMap5026 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5026 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5026_checked : acceptsGraphIso
    (source (graph core5026) (root 10) 2 2) DegreeTwoThreeSpectrum7627.graph sourceMap5026=true := by decide +kernel
theorem fusedMap5026_checked : acceptsGraphIso
    (fused (graph core5026) (root 10) 2 2) DegreeTwoThreeSpectrum6469.graph fusedMap5026=true := by decide +kernel
theorem certified5026 : Certified (graph core5026) (root 10) 2 2 :=
  of_native_maps core5026 DegreeTwoThreeSpectrum7627.graph DegreeTwoThreeSpectrum6469.graph
    sourceMap5026 fusedMap5026 sourceMap5026_checked fusedMap5026_checked
    DegreeTwoThreeFiniteComparisons.comparison5026
#print axioms sourceMap5026_checked
#print axioms fusedMap5026_checked
#print axioms certified5026
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
