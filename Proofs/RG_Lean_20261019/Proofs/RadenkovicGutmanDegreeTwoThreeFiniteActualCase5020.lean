/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5020 : Family 10 := level10.get ⟨1665,by decide⟩
def sourceMap5020 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5020 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5020_checked : acceptsGraphIso
    (source (graph core5020) (root 10) 2 2) DegreeTwoThreeSpectrum7621.graph sourceMap5020=true := by decide +kernel
theorem fusedMap5020_checked : acceptsGraphIso
    (fused (graph core5020) (root 10) 2 2) DegreeTwoThreeSpectrum6282.graph fusedMap5020=true := by decide +kernel
theorem certified5020 : Certified (graph core5020) (root 10) 2 2 :=
  of_native_maps core5020 DegreeTwoThreeSpectrum7621.graph DegreeTwoThreeSpectrum6282.graph
    sourceMap5020 fusedMap5020 sourceMap5020_checked fusedMap5020_checked
    DegreeTwoThreeFiniteComparisons.comparison5020
#print axioms sourceMap5020_checked
#print axioms fusedMap5020_checked
#print axioms certified5020
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
