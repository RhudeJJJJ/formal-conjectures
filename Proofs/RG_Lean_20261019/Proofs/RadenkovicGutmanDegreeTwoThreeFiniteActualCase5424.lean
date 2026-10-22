/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5424 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5424 : (Vertices 2 ⊕ Fin 6 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,8,9,2,3,4,5,6,7,0,10,11,12,13,14,15,16] (sourceLabel 2 5 7 v)
def fusedMap5424 : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 5 7 v)
theorem sourceMap5424_checked : acceptsGraphIso
    (source (graph core5424) (root 2) 5 7) DegreeTwoThreeSpectrum5130.graph sourceMap5424=true := by decide +kernel
theorem fusedMap5424_checked : acceptsGraphIso
    (fused (graph core5424) (root 2) 5 7) DegreeTwoThreeSpectrum4959.graph fusedMap5424=true := by decide +kernel
theorem certified5424 : Certified (graph core5424) (root 2) 5 7 :=
  of_native_maps core5424 DegreeTwoThreeSpectrum5130.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5424 fusedMap5424 sourceMap5424_checked fusedMap5424_checked
    DegreeTwoThreeFiniteComparisons.comparison5424
#print axioms sourceMap5424_checked
#print axioms fusedMap5424_checked
#print axioms certified5424
def sourceMap5424swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,8,9,0,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 2 7 5 v)
def fusedMap5424swap : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 7 5 v)
theorem sourceMap5424swap_checked : acceptsGraphIso
    (source (graph core5424) (root 2) 7 5) DegreeTwoThreeSpectrum5130.graph sourceMap5424swap=true := by decide +kernel
theorem fusedMap5424swap_checked : acceptsGraphIso
    (fused (graph core5424) (root 2) 7 5) DegreeTwoThreeSpectrum4959.graph fusedMap5424swap=true := by decide +kernel
theorem certified5424swap : Certified (graph core5424) (root 2) 7 5 :=
  of_native_maps core5424 DegreeTwoThreeSpectrum5130.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5424swap fusedMap5424swap sourceMap5424swap_checked fusedMap5424swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5424
#print axioms sourceMap5424swap_checked
#print axioms fusedMap5424swap_checked
#print axioms certified5424swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
