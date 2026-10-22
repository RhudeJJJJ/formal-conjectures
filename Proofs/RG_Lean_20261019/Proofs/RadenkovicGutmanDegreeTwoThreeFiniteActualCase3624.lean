/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3624 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap3624 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3624 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3624_checked : acceptsGraphIso
    (source (graph core3624) (root 8) 0 6) DegreeTwoThreeSpectrum6590.graph sourceMap3624=true := by decide +kernel
theorem fusedMap3624_checked : acceptsGraphIso
    (fused (graph core3624) (root 8) 0 6) DegreeTwoThreeSpectrum5482.graph fusedMap3624=true := by decide +kernel
theorem certified3624 : Certified (graph core3624) (root 8) 0 6 :=
  of_native_maps core3624 DegreeTwoThreeSpectrum6590.graph DegreeTwoThreeSpectrum5482.graph
    sourceMap3624 fusedMap3624 sourceMap3624_checked fusedMap3624_checked
    DegreeTwoThreeFiniteComparisons.comparison3624
#print axioms sourceMap3624_checked
#print axioms fusedMap3624_checked
#print axioms certified3624
def sourceMap3624swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3624swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3624swap_checked : acceptsGraphIso
    (source (graph core3624) (root 8) 6 0) DegreeTwoThreeSpectrum6590.graph sourceMap3624swap=true := by decide +kernel
theorem fusedMap3624swap_checked : acceptsGraphIso
    (fused (graph core3624) (root 8) 6 0) DegreeTwoThreeSpectrum5482.graph fusedMap3624swap=true := by decide +kernel
theorem certified3624swap : Certified (graph core3624) (root 8) 6 0 :=
  of_native_maps core3624 DegreeTwoThreeSpectrum6590.graph DegreeTwoThreeSpectrum5482.graph
    sourceMap3624swap fusedMap3624swap sourceMap3624swap_checked fusedMap3624swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3624
#print axioms sourceMap3624swap_checked
#print axioms fusedMap3624swap_checked
#print axioms certified3624swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
