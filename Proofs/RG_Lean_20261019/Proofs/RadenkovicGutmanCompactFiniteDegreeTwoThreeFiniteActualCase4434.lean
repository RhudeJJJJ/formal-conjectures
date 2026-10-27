/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4434 : Family 10 := level10.get ⟨25,by decide⟩
def sourceMap4434 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4434 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4434_checked : acceptsGraphIso
    (source (graph core4434) (root 10) 2 2) DegreeTwoThreeSpectrum5647.graph sourceMap4434=true := by decide +kernel
theorem fusedMap4434_checked : acceptsGraphIso
    (fused (graph core4434) (root 10) 2 2) DegreeTwoThreeSpectrum5046.graph fusedMap4434=true := by decide +kernel
theorem certified4434 : Certified (graph core4434) (root 10) 2 2 :=
  of_native_maps core4434 DegreeTwoThreeSpectrum5647.graph DegreeTwoThreeSpectrum5046.graph
    sourceMap4434 fusedMap4434 sourceMap4434_checked fusedMap4434_checked
    DegreeTwoThreeFiniteComparisons.comparison4434
#print axioms sourceMap4434_checked
#print axioms fusedMap4434_checked
#print axioms certified4434
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
