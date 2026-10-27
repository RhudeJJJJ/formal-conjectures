/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4443 : Family 10 := level10.get ⟨72,by decide⟩
def sourceMap4443 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4443 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4443_checked : acceptsGraphIso
    (source (graph core4443) (root 10) 2 2) DegreeTwoThreeSpectrum6415.graph sourceMap4443=true := by decide +kernel
theorem fusedMap4443_checked : acceptsGraphIso
    (fused (graph core4443) (root 10) 2 2) DegreeTwoThreeSpectrum4986.graph fusedMap4443=true := by decide +kernel
theorem certified4443 : Certified (graph core4443) (root 10) 2 2 :=
  of_native_maps core4443 DegreeTwoThreeSpectrum6415.graph DegreeTwoThreeSpectrum4986.graph
    sourceMap4443 fusedMap4443 sourceMap4443_checked fusedMap4443_checked
    DegreeTwoThreeFiniteComparisons.comparison4443
#print axioms sourceMap4443_checked
#print axioms fusedMap4443_checked
#print axioms certified4443
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
