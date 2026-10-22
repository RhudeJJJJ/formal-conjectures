/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4005 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap4005 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4005 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4005_checked : acceptsGraphIso
    (source (graph core4005) (root 6) 1 6) DegreeTwoThreeSpectrum4346.graph sourceMap4005=true := by decide +kernel
theorem fusedMap4005_checked : acceptsGraphIso
    (fused (graph core4005) (root 6) 1 6) DegreeTwoThreeSpectrum3946.graph fusedMap4005=true := by decide +kernel
theorem certified4005 : Certified (graph core4005) (root 6) 1 6 :=
  of_native_maps core4005 DegreeTwoThreeSpectrum4346.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap4005 fusedMap4005 sourceMap4005_checked fusedMap4005_checked
    DegreeTwoThreeFiniteComparisons.comparison4005
#print axioms sourceMap4005_checked
#print axioms fusedMap4005_checked
#print axioms certified4005
def sourceMap4005swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,15,9,10] (sourceLabel 6 6 1 v)
def fusedMap4005swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4005swap_checked : acceptsGraphIso
    (source (graph core4005) (root 6) 6 1) DegreeTwoThreeSpectrum4346.graph sourceMap4005swap=true := by decide +kernel
theorem fusedMap4005swap_checked : acceptsGraphIso
    (fused (graph core4005) (root 6) 6 1) DegreeTwoThreeSpectrum3946.graph fusedMap4005swap=true := by decide +kernel
theorem certified4005swap : Certified (graph core4005) (root 6) 6 1 :=
  of_native_maps core4005 DegreeTwoThreeSpectrum4346.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap4005swap fusedMap4005swap sourceMap4005swap_checked fusedMap4005swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4005
#print axioms sourceMap4005swap_checked
#print axioms fusedMap4005swap_checked
#print axioms certified4005swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
