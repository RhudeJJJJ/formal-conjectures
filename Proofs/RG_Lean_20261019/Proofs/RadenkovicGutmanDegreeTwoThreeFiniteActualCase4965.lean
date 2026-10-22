/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4965 : Family 10 := level10.get ⟨1538,by decide⟩
def sourceMap4965 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4965 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4965_checked : acceptsGraphIso
    (source (graph core4965) (root 10) 2 2) DegreeTwoThreeSpectrum7566.graph sourceMap4965=true := by decide +kernel
theorem fusedMap4965_checked : acceptsGraphIso
    (fused (graph core4965) (root 10) 2 2) DegreeTwoThreeSpectrum5982.graph fusedMap4965=true := by decide +kernel
theorem certified4965 : Certified (graph core4965) (root 10) 2 2 :=
  of_native_maps core4965 DegreeTwoThreeSpectrum7566.graph DegreeTwoThreeSpectrum5982.graph
    sourceMap4965 fusedMap4965 sourceMap4965_checked fusedMap4965_checked
    DegreeTwoThreeFiniteComparisons.comparison4965
#print axioms sourceMap4965_checked
#print axioms fusedMap4965_checked
#print axioms certified4965
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
