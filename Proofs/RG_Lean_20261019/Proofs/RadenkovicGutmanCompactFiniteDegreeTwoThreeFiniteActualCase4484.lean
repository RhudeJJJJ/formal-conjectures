/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4484 : Family 10 := level10.get ⟨234,by decide⟩
def sourceMap4484 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4484 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4484_checked : acceptsGraphIso
    (source (graph core4484) (root 10) 2 2) DegreeTwoThreeSpectrum6328.graph sourceMap4484=true := by decide +kernel
theorem fusedMap4484_checked : acceptsGraphIso
    (fused (graph core4484) (root 10) 2 2) DegreeTwoThreeSpectrum5293.graph fusedMap4484=true := by decide +kernel
theorem certified4484 : Certified (graph core4484) (root 10) 2 2 :=
  of_native_maps core4484 DegreeTwoThreeSpectrum6328.graph DegreeTwoThreeSpectrum5293.graph
    sourceMap4484 fusedMap4484 sourceMap4484_checked fusedMap4484_checked
    DegreeTwoThreeFiniteComparisons.comparison4484
#print axioms sourceMap4484_checked
#print axioms fusedMap4484_checked
#print axioms certified4484
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
