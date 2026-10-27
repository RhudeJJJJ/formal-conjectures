/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4380 : Family 9 := level9.get ⟨552,by decide⟩
def sourceMap4380 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4380 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4380_checked : acceptsGraphIso
    (source (graph core4380) (root 9) 2 2) DegreeTwoThreeSpectrum4907.graph sourceMap4380=true := by decide +kernel
theorem fusedMap4380_checked : acceptsGraphIso
    (fused (graph core4380) (root 9) 2 2) DegreeTwoThreeSpectrum4184.graph fusedMap4380=true := by decide +kernel
theorem certified4380 : Certified (graph core4380) (root 9) 2 2 :=
  of_native_maps core4380 DegreeTwoThreeSpectrum4907.graph DegreeTwoThreeSpectrum4184.graph
    sourceMap4380 fusedMap4380 sourceMap4380_checked fusedMap4380_checked
    DegreeTwoThreeFiniteComparisons.comparison4380
#print axioms sourceMap4380_checked
#print axioms fusedMap4380_checked
#print axioms certified4380
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
