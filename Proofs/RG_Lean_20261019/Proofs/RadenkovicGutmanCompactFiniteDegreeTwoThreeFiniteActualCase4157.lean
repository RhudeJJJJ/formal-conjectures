/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4157 : Family 8 := level8.get ⟨181,by decide⟩
def sourceMap4157 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 2 2 v)
def fusedMap4157 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4157_checked : acceptsGraphIso
    (source (graph core4157) (root 8) 2 2) DegreeTwoThreeSpectrum3531.graph sourceMap4157=true := by decide +kernel
theorem fusedMap4157_checked : acceptsGraphIso
    (fused (graph core4157) (root 8) 2 2) DegreeTwoThreeSpectrum2953.graph fusedMap4157=true := by decide +kernel
theorem certified4157 : Certified (graph core4157) (root 8) 2 2 :=
  of_native_maps core4157 DegreeTwoThreeSpectrum3531.graph DegreeTwoThreeSpectrum2953.graph
    sourceMap4157 fusedMap4157 sourceMap4157_checked fusedMap4157_checked
    DegreeTwoThreeFiniteComparisons.comparison4157
#print axioms sourceMap4157_checked
#print axioms fusedMap4157_checked
#print axioms certified4157
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
