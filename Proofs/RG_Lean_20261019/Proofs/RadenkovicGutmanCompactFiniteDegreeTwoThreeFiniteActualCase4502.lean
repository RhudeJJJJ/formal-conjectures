/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4502 : Family 10 := level10.get ⟨294,by decide⟩
def sourceMap4502 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4502 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4502_checked : acceptsGraphIso
    (source (graph core4502) (root 10) 2 2) DegreeTwoThreeSpectrum6558.graph sourceMap4502=true := by decide +kernel
theorem fusedMap4502_checked : acceptsGraphIso
    (fused (graph core4502) (root 10) 2 2) DegreeTwoThreeSpectrum5458.graph fusedMap4502=true := by decide +kernel
theorem certified4502 : Certified (graph core4502) (root 10) 2 2 :=
  of_native_maps core4502 DegreeTwoThreeSpectrum6558.graph DegreeTwoThreeSpectrum5458.graph
    sourceMap4502 fusedMap4502 sourceMap4502_checked fusedMap4502_checked
    DegreeTwoThreeFiniteComparisons.comparison4502
#print axioms sourceMap4502_checked
#print axioms fusedMap4502_checked
#print axioms certified4502
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
