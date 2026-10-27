/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4521 : Family 10 := level10.get ⟨360,by decide⟩
def sourceMap4521 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4521 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4521_checked : acceptsGraphIso
    (source (graph core4521) (root 10) 2 2) DegreeTwoThreeSpectrum6786.graph sourceMap4521=true := by decide +kernel
theorem fusedMap4521_checked : acceptsGraphIso
    (fused (graph core4521) (root 10) 2 2) DegreeTwoThreeSpectrum5642.graph fusedMap4521=true := by decide +kernel
theorem certified4521 : Certified (graph core4521) (root 10) 2 2 :=
  of_native_maps core4521 DegreeTwoThreeSpectrum6786.graph DegreeTwoThreeSpectrum5642.graph
    sourceMap4521 fusedMap4521 sourceMap4521_checked fusedMap4521_checked
    DegreeTwoThreeFiniteComparisons.comparison4521
#print axioms sourceMap4521_checked
#print axioms fusedMap4521_checked
#print axioms certified4521
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
