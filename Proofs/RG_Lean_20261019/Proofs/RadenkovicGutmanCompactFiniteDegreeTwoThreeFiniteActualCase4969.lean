/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4969 : Family 10 := level10.get ⟨1548,by decide⟩
def sourceMap4969 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4969 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4969_checked : acceptsGraphIso
    (source (graph core4969) (root 10) 2 2) DegreeTwoThreeSpectrum7570.graph sourceMap4969=true := by decide +kernel
theorem fusedMap4969_checked : acceptsGraphIso
    (fused (graph core4969) (root 10) 2 2) DegreeTwoThreeSpectrum5999.graph fusedMap4969=true := by decide +kernel
theorem certified4969 : Certified (graph core4969) (root 10) 2 2 :=
  of_native_maps core4969 DegreeTwoThreeSpectrum7570.graph DegreeTwoThreeSpectrum5999.graph
    sourceMap4969 fusedMap4969 sourceMap4969_checked fusedMap4969_checked
    DegreeTwoThreeFiniteComparisons.comparison4969
#print axioms sourceMap4969_checked
#print axioms fusedMap4969_checked
#print axioms certified4969
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
